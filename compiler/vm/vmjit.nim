## Implements the framework for just-in-time (JIT) code-generation
## for the VM. Both procedures and standalone statements/expressions are
## supported as input.
##
## When a procedure is requested that hasn't been processed by the JIT
## compiler, it is transformed, pre-processed (MIR passes applied, etc.), and
## then the bytecode for it is generated. If code generation succeeds, all not-
## already-seen dependencies (like globals, constants, etc.) of the procedure
## are collected, registered with the JIT state, and loaded into the VM's
## execution environment, meaning that the requested procedure can be
## immediately invoked after.
##
## Both compile-time code execution and running NimScript files make use of
## the JIT compiler.

import
  std/[
    tables,
    options
  ],
  compiler/ast/[
    ast_idgen,
    ast_types,
    ast_query,
  ],
  compiler/backend/[
    backends,
    cgir
  ],
  compiler/front/[
    in_options,
  ],
  compiler/mir/[
    datatables,
    mirbodies,
    mirbridge,
    mirenv,
    mirgen,
    mirpasses,
    mirtrees,
    mirtypes
  ],
  compiler/modules/[
    magicsys,
    modulegraphs
  ],
  compiler/sem/[
    transf
  ],
  compiler/vm/[
    identpatterns,
    vmaux,
    vmserialize,
    vmdef,
    vmgen,
    vmtypes,
    vmalloc,
    vmjit_checks,
    # vmmemory,
    vmtypegen,
    vmutils
  ],
  compiler/utils/[
    containers
  ],
  experimental/[
    results
  ]

# XXX: temporary imports for expression support
from compiler/ast/ast import newTreeIT
from compiler/sem/semdata import makeVarType
from compiler/sem/parampatterns import isAssignable, TAssignableResult

export VmGenResult

type
  JitState* = object
    ## State of the VM's just-in-time compiler that is kept across invocations.
    gen: CodeGenCtx
      ## code generator state

    idgen*: IdGenerator
      ## needed for some legacy CGIR reasons, but should ideally be removed
    module*: PSym
      ## provides the contextual information for non-procedure code

    callbackKeys: seq[IdentPattern]

    flags*: set[CodeGenFlag]
    mode*: TEvalMode

  JitResult* = Result[VmFunctionPtr, VmGenDiag]

proc initJit*(graph: ModuleGraph): JitState =
  ## Returns an initialized ``JitState`` instance.
  JitState(gen: initCodeGen(graph))

template graph*(jit: JitState): ModuleGraph =
  jit.gen.graph

template config*(jit: JitState): untyped =
  jit.gen.config

func env*(jit: JitState): lent MirEnv {.inline.} =
  ## The JIT code generator's MIR environment.
  jit.gen.env

func selectOptions(c: JitState): TranslationConfig =
  result = TranslationConfig(options: {goIsNimvm}, magicsToKeep: MagicsToKeep)
  # include additional options based on the JIT's configuration
  if cgfAllowMeta in c.flags:
    result.options.incl goGenTypeExpr

  if c.mode in {emConst, emOptimize, emStaticExpr, emStaticStmt}:
    result.options.incl goIsCompileTime

func swapState(c: var TCtx, gen: var CodeGenCtx) =
  ## Swaps the values of the fields shared between `TCtx` and `CodeGenCtx`.
  ## This achieves reasonably fast mutable-borrow-like semantics without
  ## resorting to pointers.
  template swap(field: untyped) =
    swap(c.field, gen.field)

  # input-output parameters:
  swap(code)
  swap(debug)
  swap(ehTable)
  swap(ehCode)
  swap(constants)
  swap(types)

proc updateEnvironment(c: var TCtx, gen: var CodeGenCtx, cp: EnvCheckpoint) =
  ## Needs to be called after a `vmgen` invocation and prior to resuming
  ## execution. Allocates and sets up the execution resources required for the
  ## newly gathered dependencies (those added since `cp` was created).
  ##
  ## This "commits" to the new dependencies.
  template env: MirEnv = gen.env

  # globals (which includes threadvars)
  for id, sym in since(env.globals, cp.globals):
    let typ = gen.typeInfoCache.getOrCreate(c.types, gen.config, sym.typ, false)
    c.globals[0].add (typ, cast[StackValue](c.allocator.alloc0(c.types[typ].size, typ)))

  # constants
  for id, data in since(env.data, cp.data):
    let
      typ = gen.typeInfoCache.getOrCreate(c.types, gen.config, env.types[data[0].typ], false)
      p = c.allocator.alloc0(c.types[typ].size, typ)

    initFromExpr(c.allocator.translate(p), typ, data, env, gen.config, c)

    c.globals[1].add (typ, cast[StackValue](p))

template preCheck(env: MirEnv, n: PNode) =
  ## Verifies that `n` can be built and run in JIT mode. If not, aborts the
  ## surrounding routine by returning early.
  block:
    let r = validate(env, n)
    if r.isErr:
      result = typeof(result).err(r.takeErr)
      return

func removeLastEof(c: var VmEnv) =
  let last = c.code.len-1
  if last >= 0 and c.code[last].opcode == opcRet:
    # overwrite last EOF:
    assert c.code.len == c.debug.len
    c.code.setLen(last)
    c.debug.setLen(last)

proc generateMirCode(c: var JitState, n: PNode; isStmt = false): MirBody =
  ## Generates the initial MIR code for a standalone statement/expression.
  if isStmt:
    result = generateCode(c.graph, c.gen.env, c.module, selectOptions(c), n)
  else:
    var n = n
    # optimization: wrap the expression in a hidden address if it's an lvalue
    # expression. This eliminates the unnecessary copy that would be created
    # otherwise
    if isAssignable(nil, n, isUnsafeAddr=true) in {arLocalLValue, arLValue,
                                                   arLentValue}:
      n = newTreeIT(nkHiddenAddr, n.info,
                    makeVarType(c.module, n.typ, c.idgen, tyLent),
                    n)

    result = exprToMir(c.graph, c.gen.env, selectOptions(c), n)

proc generateIR(c: var JitState, body: sink MirBody): Body =
  backends.generateIR(c.graph, c.idgen, c.gen.env, c.module, body)

proc setupRootRef(c: var CodeGenCtx) =
  ## Sets up if the ``RootRef`` type for the type info cache. This
  ## is a temporary workaround, refer to the documentation of the
  ## ``rootRef`` field.
  if c.typeInfoCache.rootRef == vmtypes.VoidType:
    let t = c.graph.getCompilerProc("RootObj")
    # the``RootObj`` type may not be available yet
    if t != nil:
      let root = c.getOrCreate(t.typ)
      initRootRef(c.types, c.typeInfoCache, c.graph.config, root)

template runCodeGen(c: var TCtx, cg: var CodeGenCtx, b: Body,
                    body: untyped): untyped =
  ## Prepares the code generator's context and then executes `body`. A
  ## delimiting 'eof' instruction is emitted at the end.
  swapState(c, cg)
  setupRootRef(cg)
  let info = b.code.info
  let r = body
  cg.instr(info, opcRet)
  swapState(c, cg)
  r

proc applyPasses(g: ModuleGraph, env: var MirEnv, prc: PSym, body: var MirBody) =
  let restore = optProfiler in prc.options
  # don't instrument procedures when using the JIT
  if restore:
    prc.options.excl optProfiler
  applyPasses(body, prc, env, g, targetVm)
  if restore:
    prc.options.incl optProfiler

proc register(c: var VmEnv, cg: var CodeGenCtx, n: MirNode) =
  ## If `n` refers to a procedure, registers it in the execution environment's
  ## procedure table.
  if n.kind == mnkProc:
    let s = cg.env[n.prc]
    let typ =
      if s.kind == skMacro:
        cg.typeInfoCache.getOrCreate(c.types, cg.config, s.internal, noClosure=true)
      else:
        cg.typeInfoCache.getOrCreate(c.types, cg.config, s.typ, noClosure=true)
    c.procs.add initProcEntry(s, typ)
    cg.map[n.prc] = c.procs.high.FunctionIndex

proc gen(jit: var JitState, c: var VmEnv, n: PNode, isStmt: bool): JitResult =
  preCheck(jit.gen.env, n)
  c.removeLastEof()

  let cp = checkpoint(jit.gen.env)

  # `n` is expected to have been put through ``transf`` already
  var mirBody = generateMirCode(jit, n, isStmt)
  applyPasses(jit.graph, jit.gen.env, jit.module, mirBody)
  for item in discover(jit.gen.env, cp):
    register(c, jit.gen, item.n)

  let
    rtyp = jit.gen.typeInfoCache.createProcType(jit.gen.config, c.types, jit.gen.env[mirBody[resultId].typ])
    body = generateIR(jit, mirBody)
    start = c.code.len

  # generate the bytecode:
  let r = runCodeGen(c, jit.gen, body): genStmt(jit.gen, body)

  if unlikely(r.isErr):
    rewind(jit.gen.env, cp)
    return JitResult.err(r.takeErr)

  updateEnvironment(c, jit.gen, cp)

  c.procs.add ProcEntry(kind: ckDefault, start: start, typ: rtyp, locals: newSeq[AtomKind](r.get))
  result.initSuccess(c.procs.len.VmFunctionPtr)

proc genStmt*(jit: var JitState, c: var TCtx, n: PNode): JitResult =
  ## Generates and emits code for the standalone top-level statement `n`.
  gen(jit, c, n, isStmt = true)

proc genExpr*(jit: var JitState, c: var TCtx, n: PNode): JitResult =
  ## Generates and emits code for the standalone expression `n`
  gen(jit, c, n, isStmt = false)

proc genProc(jit: var JitState, c: var TCtx, s: PSym): VmGenResult =
  let body =
    if isCompileTimeProc(s) and not defined(nimsuggest):
      # no need to go through the transformation cache
      transformBody(jit.graph, jit.idgen, s, s.ast[bodyPos])
    else:
      # watch out! Since transforming a procedure body permanently alters
      # the state of inner procedures, we need to both cache and later
      # retrieve the transformed body for non-compile-only routines or
      # when in suggest mode
      transformBody(jit.graph, jit.idgen, s, cache = true)

  preCheck(jit.gen.env, body)
  c.removeLastEof()

  let cp = checkpoint(jit.gen.env)

  echoInput(jit.config, s, body)
  var mirBody = generateCode(jit.graph, jit.gen.env, s, selectOptions(jit), body)
  echoMir(jit.config, s, mirBody, jit.gen.env)
  applyPasses(jit.graph, jit.gen.env, s, mirBody)
  for item in discover(jit.gen.env, cp):
    register(c, jit.gen, item.n)

  let outBody = generateIR(jit.graph, jit.idgen, jit.gen.env, s, mirBody)

  # generate the bytecode:
  result = runCodeGen(c, jit.gen, outBody): genProc(jit.gen, s, outBody)

  if unlikely(result.isErr):
    rewind(jit.gen.env, cp)
    return

  updateEnvironment(c, jit.gen, cp)

func getGlobal*(jit: JitState, g: PSym): LinkIndex =
  ## Returns the link index for the symbol `g`. `g` must be known to `jit`.
  LinkIndex jit.gen.env.globals[g]

func isAvailable*(jit: JitState, c: TCtx, prc: PSym): bool =
  ## Returns whether the bytecode for `prc` is already available.
  prc in jit.gen.env.procedures and
    c.procs[jit.gen.env.procedures[prc].int].kind != ckStub

proc registerProcedure*(jit: var JitState, c: var TCtx, prc: PSym): FunctionIndex =
  ## If it hasn't been already, adds `prc` to the set of procedures the JIT
  ## code-generator knowns about and sets up a function-table entry. `jit` is
  ## required to not be in the process of generating code.
  if prc notin jit.gen.env.procedures:
    let id = jit.gen.env.procedures.add(prc)
    register(c, jit.gen, MirNode(kind: mnkProc, prc: id))
    result = c.procs.high.FunctionIndex
  else:
    result = jit.gen.map[jit.gen.env.procedures[prc]]

import compiler/vm/vmvalidation

# proc handleMagic(jit: JitState, sym: PSym): int =
#   case sym.magic
#   of mSetLengthStr:
#     result = jit.callbackKeys.lookup("__builtin_strSetLen")
#   else:
#     result = -1

proc compile*(jit: var JitState, c: var TCtx, fnc: FunctionIndex): JitResult =
  ## Generates code for the the given function and updates the execution
  ## environment. In addition, the function's table entry is updated with the
  ## bytecode position and execution requirements (i.e. register count). Make
  ## sure to only use `compile` when you're sure the function wasn't generated
  ## yet
  assert c.procs[fnc.int].kind == ckStub, "proc already generated"

  let idx = lookup(jit.callbackKeys, c.procs[fnc.int].sym)
  if idx != -1:
    # the procedure is redirected to a syscall
    c.procs[fnc.int].kind = ckCallback
    c.procs[fnc.int].cbOffset = idx
    return JitResult.ok(toFuncPtr fnc)

  if importcCond(jit.graph, c.procs[fnc.int].sym):
    # TODO: proper error
    return JitResult.err(VmGenDiag())

  let r = genProc(jit, c, c.procs[fnc.int].sym)
  if unlikely(r.isErr):
    return JitResult.err(r.takeErr())

  fillProcEntry(c.procs[fnc.int], r.unsafeGet)

  if not validate(c, fnc, c.code[r.unsafeGet.start..^2]):
    echo "------- validate"
    let listing = codeListing(c, r.unsafeGet.start)
    echo renderCodeListing(jit.config, nil, listing)
    return JitResult.err(VmGenDiag())

  result.initSuccess(fnc.toFuncPtr)

proc loadProc*(jit: var JitState, c: var TCtx, sym: PSym): JitResult =
  ## The main entry point into the JIT code-generator. Retrieves the
  ## information required for executing `sym`. A function table entry is
  ## created first if it doesn't exist yet, and the procedure is also
  ## generated via `compile` if it wasn't already
  let
    idx = jit.registerProcedure(c, sym)

  if c.procs[idx.int].kind != ckStub:
    JitResult.ok(idx.toFuncPtr)
  else:
    compile(jit, c, idx)

import compiler/vm/vmbuiltins

proc registerCallback*(jit: var JitState, c: var TCtx; pattern: string; callback: VmCallback) =
  ## Registers the `callback` with `c`. After the ``registerCallback`` call,
  ## when a procedures of which the fully qualified identifier matches
  ## `pattern` is added to the VM's function table, all invocations of the
  ## procedure at run-time will invoke the callback instead.
  # XXX: consider renaming this procedure to ``registerOverride``
  if c.callbacks.len == 0:
    for key, cb in builtins():
      c.callbacks.add(cb)
      c.procs.add ProcEntry(kind: ckCallback, cbOffset: c.callbacks.high)
      jit.gen.builtinMaps[key] = c.procs.high.FunctionIndex
      jit.callbackKeys.add(IdentPattern("__magic__." & key))

  c.callbacks.add(callback) # some consumers rely on preserving registration order
  jit.callbackKeys.add(IdentPattern(pattern))
  assert c.callbacks.len == jit.callbackKeys.len

proc constDataToMir*(c: var TCtx, jit: var JitState, e: PNode): MirTree =
  ## Translates the constant expression `e` to a MIR constant expression and
  ## returns it. Entities referenced by the constant expression (e.g.,
  ## procedures), are direclty registered with the environment.
  let cp = checkpoint(jit.gen.env)
  result = constDataToMir(jit.gen.env, e)

  # run the discovery pass:
  for _ in discover(jit.gen.env, cp):
    discard "nothing to register"

  # populate the VM environment with the discovered entities:
  updateEnvironment(c, jit.gen, cp)
