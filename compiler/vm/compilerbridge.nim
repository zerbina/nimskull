## This module implements the interface between the VM and the rest of the
## compiler. The VM is only interacted with through this interface. Do note
## that right now, the compiler still indirectly interacts with the VM through
## the ``vmdef.TCtx`` object.
##
## The interface includes:
## - the procedure that sets up a VM instance for use during compilation
##   (``setupGlobalCtx``)
## - the routines for executing expressions, statements, and macros with the VM
## - an implementation of the ``passes`` interface that executes processed
##   code with the VM (``evalPass``)
## - the VM-related compilerapi

import
  std/[
    tables
  ],
  compiler/ast/[
    renderer,
    ast_types,
    ast,
    errorhandling,
    errorreporting,
    lineinfos,
    trees
  ],
  compiler/front/[
    msgs,
    options
  ],
  compiler/mir/[
    mirenv,
    mirtrees
  ],
  compiler/modules/[
    modulegraphs
  ],
  compiler/sem/[
    passes,
    semcomptime,
    transf
  ],
  compiler/utils/[
    debugutils,
    idioms,
    astrepr
  ],
  compiler/vm/[
    vmcompilerserdes,
    vmdef,
    vmhooks,
    vmjit,
    vmlegacy,
    vmconv,
    vmops,
    macroapi,
    vmprofiler,
    vmserialize,
    vmtypegen,
    vmalloc,
    vmutils,
    vmtypes,
    newvm,
    vmdebug
  ],
  experimental/[
    results
  ]

import std/options as std_options

from std/strutils import join
from std/times import cpuTime

from compiler/vm/vmgen import vmGenDiagToAstDiagVmGenError

# TODO: legacy report cruft remove from here
from compiler/ast/reports import wrap, toReportLineInfo
from compiler/ast/reports_vm import VMReport
from compiler/ast/reports_sem import SemReport
from compiler/ast/reports_internal import InternalReport
from compiler/ast/report_enums import ReportKind

type
  ExecErrorKind* = enum
    execErrorVm
    execErrorVmGen
    execErrorQuit

  ExecErrorReport* = object
    stackTrace*: VmStackTrace   ## The VM stack-trace
    location*: TLineInfo        ## Source location of the trace
    instLoc*: InstantiationInfo ## report instantiation location
    case kind*: ExecErrorKind   ## kind of error execution of vm code gen
      of execErrorVm:
        vmErr*: VmEvent
      of execErrorVmGen:
        genErr*: VmGenDiag
      of execErrorQuit:
        exitCode*: int

  ExecutionResult* = Result[PNode, ExecErrorReport]

  PEvalContext* = ref EvalContext
  EvalContext* {.final.} = object of RootObj
    ## All state required to on-demand translate AST to VM bytecode and execute
    ## it. An ``EvalContext`` instance makes up everything that is required
    ## for running code at compile-time.
    vm*: TCtx
    jit*: JitState
    iface: CompilerIface

  PDelayedVm* = ref object of RootObj
    ## Wrapper type intended for storing only a VM instance (without a JIT
    ## environment) in the module graph.
    mode*: TEvalMode
    flags*: set[CodeGenFlag]
    # overrides*: seq[Override]

  PEvalPassContext = ref object of PPassContext
    ## Pass context for the evaluation pass.
    graph: ModuleGraph
    module: PSym
    oldErrorCount: int

# prevent a default `$` implementation from being generated
func `$`(e: ExecErrorReport): string {.error.}
func vmEventToAstDiagVmError*(evt: VmEvent): AstDiagVmError {.inline.}

proc logBytecode(config: ConfigRef, c: TCtx, owner: PSym, start: int) =
  ## If enabled, renders the bytecode ranging from `start` to the current end
  ## into text that is then written to the standard output.
  if irVm in config.toDebugIr or
     (owner != nil and config.isDebugEnabled(irVm, owner.name.s)):
    let listing = codeListing(c, start)
    echo renderCodeListing(config, nil, listing)

proc logBytecode(config: ConfigRef, c: TCtx, prc: FunctionIndex) =
  if c.procs[prc.int].kind == ckDefault:
    logBytecode(config, c, c.procs[prc.int].sym, c.procs[prc.int].start)

proc putIntoReg(jit: var JitState, c: var TCtx, n: PNode, typ: VmTypeId,
                formal: PType): StackValue =
  ## Treats `n` as a constant expression and loads the value it represents
  ## into `dest`.
  let data = constDataToMir(c, jit, n)
  case c.types[typ].kind
  of akInt:
    result = cast[StackValue](jit.env.getInt(data[0].number))
  of akFloat:
    result = cast[StackValue](jit.env.getFloat(data[0].number))
  of akPtr:
    # non-nil values should have already been reported as an error
    assert data[0].kind == mnkNilLit
  of akForeign:
    result = cast[StackValue](c.allocator.register(jit.env[data[0].ast]))
  else:
    # TODO: use the stack allocator
    result = cast[StackValue](c.allocator.alloc0(c.types[typ].size))
    initFromExpr(c.allocator.translate(VirtualAddr result), typ, data, jit.env, jit.config, c)

# proc check(n: PNode, i: int) =
#   echo i, ": ", n.kind
#   case n.kind
#   of nkWithoutSons:
#     discard
#   of nkWithSons:
#     for i in 0..<n.len:
#       check(n[i], i)

proc regToNode(c: TCtx, config: ConfigRef, p: VmTypeId, val: StackValue; typ: PType, info: TLineInfo): PNode =
  ## Deserializes the value stored by `x` to a `PNode` of type `typ`
  case c.types[p].kind
  of akInt:
    result = newIntTypeNode(cast[BiggestInt](val), typ)
  of akFloat:
    result = newNodeIT(nkFloatLit, info, typ)
    result.floatVal = cast[BiggestFloat](val)
  of akPtr:
    if uint64(val) == 0:
      result = newNodeIT(nkNilLit, info, typ)
    else:
      var h: HostPointer
      # TODO: a typecheck would make sense
      if checkmem(c.allocator, VirtualAddr(val), c.types[c.types[p].a].size, h):
        return config.newError(newNodeI(nkEmpty, info), PAstDiag(kind: adVmDerefAccessOutOfBounds))

      result = c.deserialize(config, h, c.types[p].a, typ, info)
  of akForeign:
    # TODO: validate the foreign ref
    result = c.allocator.lookup(ForeignRef(val), PNode)
    # check(result, 0)
  else:
    var h: HostPointer
    if checkmem(c.allocator, cast[VirtualAddr](val), c.types[p].size, h):
      return config.newError(newNodeI(nkEmpty, info), PAstDiag(kind: adVmDerefAccessOutOfBounds))
    result = c.deserialize(config, h, p, typ, info)

  assert result != nil

proc unpackResult(res: sink ExecutionResult; config: ConfigRef, node: PNode): PNode =
  ## Unpacks the execution result. If the result represents a failure, returns
  ## a new `nkError` wrapping `node`. Otherwise, returns the value/tree result,
  ## optionally filling in the node's `info` with that of `node`, if not
  ## present already.
  if res.isOk:
    result = res.take
    if node != nil and result.info.line < 0:
      result.info = node.info
  else:
    let
      err = res.takeErr
      errKind = err.kind
      astDiagTrace = AstDiagVmTrace(
        currentExceptionA: err.stackTrace.currentExceptionA,
        currentExceptionB: err.stackTrace.currentExceptionB,
        stacktrace: err.stackTrace.stacktrace,
        skipped: err.stackTrace.skipped,
        location: err.location,
        instLoc: err.instLoc)
      astDiag =
        case errKind
        of execErrorVm:
          let location =
            case err.vmErr.kind
            of vmEvtUserError:         err.vmErr.errLoc
            of vmEvtArgNodeNotASymbol: err.vmErr.argAst.info
            else:                      err.location

          PAstDiag(
            kind: adVmError,
            location: location,
            instLoc: err.vmErr.instLoc,
            vmErr: vmEventToAstDiagVmError(err.vmErr),
            vmTrace: astDiagTrace)
        of execErrorVmGen:
          PAstDiag(
            kind: adVmGenError,
            location: err.genErr.location,
            instLoc: err.genErr.instLoc,
            vmGenErr: vmGenDiagToAstDiagVmGenError(err.genErr),
            duringJit: true,
            vmGenTrace: astDiagTrace)
        of execErrorQuit:
          PAstDiag(
            kind: adVmQuit,
            location: err.location,
            instLoc: err.instLoc,
            vmExitCode: err.exitCode,
            vmExitTrace: astDiagTrace)

    result = config.newError(node, astDiag, instLoc(-1))

proc createStackTrace(c: TCtx, raw: VmRawStackTrace;
                      recursionLimit: int = 100): VmStackTrace =
  ## Creates a compiler-facing stacktrace from the internal stacktrace `raw`.
  result = VmStackTrace(currentExceptionA: nil, currentExceptionB: nil)

  var count = 0
  # create the stacktrace entries:
  for i in countdown(raw.high, 0):
    let f {.cursor.} = raw[i]

    if count < recursionLimit - 1 or i == 0:
      # The `i == 0` is to make sure that we're always including the bottom of
      # the stack (the entry procedure) in the trace

      # Since we're walking the stack from top to bottom, the elements are
      # added to the trace in reverse order (the most recent procedure is
      # first in the list, not last). This needs to be accounted for by the
      # actual reporting logic
      result.stacktrace.add((sym: f.sym, location: c.debug[f.pc]))

    inc count

  if count > recursionLimit:
    result.skipped = count - recursionLimit

  assert result.stacktrace.len() <= recursionLimit # post condition check

proc buildError(c: TCtx, thread: VmThread, event: sink VmEvent): ExecErrorReport  =
  ## Creates an `ExecErrorReport` with the `event` and a stack-trace for
  ## `thread`
  let stackTrace =
    if event.kind == vmEvtUnhandledException and event.trace.len > 0:
      # HACK: an unhandled exception can be reported without providing a trace.
      #       Ideally, that shouldn't happen
      createStackTrace(c, event.trace)
    else:
      createStackTrace(c, thread)

  ExecErrorReport(
    stackTrace: stackTrace,
    instLoc: instLoc(-1),
    location: source(c, thread),
    kind: execErrorVm,
    vmErr: event)

proc buildError(c: TCtx, thread: VmThread, diag: sink VmGenDiag): ExecErrorReport  =
  ## Creates an `ExecErrorReport` with the `diag` and a stack-trace for
  ## `thread`
  ExecErrorReport(
    stackTrace: createStackTrace(c, thread),
    instLoc: instLoc(-1),
    location: source(c, thread),
    kind: execErrorVmGen,
    genErr: diag)

proc buildQuit(c: TCtx, thread: VmThread, exitCode: int): ExecErrorReport =
  ## Creates an `ExecErrorReport` with the `exitCode` and a stack-trace for
  ## `thread`
  ExecErrorReport(
    stackTrace: createStackTrace(c, thread),
    instLoc: instLoc(-1),
    location: source(c, thread),
    kind: execErrorQuit,
    exitCode: exitCode)

proc createLegacyStackTrace(
    c: TCtx,
    thread: VmThread,
    instLoc: InstantiationInfo = instLoc(-1)
  ): VMReport =
  let st = createStackTrace(c, thread)
  result = VMReport(kind: rvmStackTrace,
                    currentExceptionA: st.currentExceptionA,
                    currentExceptionB: st.currentExceptionB,
                    stacktrace: st.stacktrace,
                    skipped: st.skipped,
                    location: some source(c, thread),
                    reportInst: toReportLineInfo(instLoc))

var debug = VmDebugger(breakOn: bpYield)

proc execute(jit: var JitState, c: var TCtx, iface: CompilerIface, thread: sink VmThread,
             typ: PType, info: TLineInfo): ExecutionResult {.inline.} =
  ## This is the entry point for invoking the VM to execute code at
  ## compile-time. The `cb` callback is used to deserialize the result stored
  ## as VM data into ``PNode`` AST, and is invoked with the register that
  ## holds the result

  update(debug, c, thread.pc)
  # run the VM until either no code is left to execute or an event implying
  # execution can't go on occurs
  while true:
    var r = run(c, thread, iface)
    case r.kind
    of yrkDone:
      # execution is finished
      doAssert r.reg.isSome() or jit.mode in {emStaticStmt, emRepl},
        "non-static stmt evaluation must produce a value, mode: " & $jit.mode
      if r.reg.isSome():
        assert typ != nil
        let n = regToNode(c, jit.config, r.typ, r.reg.unsafeGet, typ, info)
        # echo "------------------- result: ", renderTree(n), " at ", jit.config.toFileLineCol(info)
        result.initSuccess n
      else:
        result.initSuccess jit.graph.emptyNode
      break
    of yrkError:
      echo "error occurred; aborting..."
      debug(debug, thread, c, jit.config)
      result.initFailure buildError(c, thread, r.error)
      break
    of yrkUnhandledException:
      var ast = newTree(nkObjConstr, newNode(nkEmpty), newNode(nkEmpty),
        newStrNode(nkStrLit, readString(c, VirtualAddr(uint64(r.exc) + 16))),
        newStrNode(nkStrLit, readString(c, VirtualAddr(uint64(r.exc) + 32))))
      var evt = VmEvent(kind: vmEvtUnhandledException, exc: ast)
      result.initFailure buildError(c, thread, evt)
      break
    of yrkMissingProcedure:
      # a stub entry was encountered -> generate the code for the
      # corresponding procedure
      let res = compile(jit, c, r.entry)
      if res.isErr:
        # code-generation failed
        result.initFailure:
          buildError(c, thread, res.takeErr)
        break
      update(debug, c, thread.pc)
      # success! ``compile`` updated the procedure's entry, so we can
      # continue execution
      logBytecode(jit.config, c, res.get.toFuncIndex)
    of yrkUser:
      case r.reason
      of 0:
        # 'echo' syscall
        var text: string
        for _ in 0..<r.args:
          # XXX: meh, lots of allocations -- refactor
          text = readString(c, VirtualAddr thread.pop()) & text
        # xxx: `localReport` and report anything needs to be replaced, this is
        #      just output and it's ridiculous that it all funnles through
        #      `cli_reporter`. Using it here only because I'm sure there is some
        #      spooky action at a distance breakage without. at least it's pushed
        #      out to the edge.
        # localReport(jit.config,
        #   InternalReport(msg: text, kind: rintEchoMessage))
        echo text
      of 1:
        # 'quit' syscall
        let exitCode = thread.pop()
        case jit.mode
        of emRepl, emStaticExpr, emStaticStmt:
          # XXX: should code run at compile time really be able to force-quit
          #      the compiler? It currently can.
          localReport(jit.config, createLegacyStackTrace(c, thread))
          localReport(jit.config, InternalReport(kind: rintQuitCalled))
          # FIXME: this will crash the compiler (RangeDefect) if `quit` is
          #        called with a value outside of int8 range!
          msgQuit(int8(exitCode))
        of emConst, emOptimize:
          result.initFailure buildQuit(c, thread, int(exitCode))
          break # terminate the loop
        of emStandalone:
          unreachable("not valid at compile-time")
      of 2:
        # breakpoint
        dec thread.pc
        debug(debug, thread, c, jit.config)
      else:
        missing("unknown syscall handling")

  dispose(c, thread)

proc execute(jit: var JitState, c: var TCtx, iface: CompilerIface, prc: FunctionIndex): ExecutionResult =
  execute(jit, c, iface, initVmThread(c, prc, @[]), nil, unknownLineInfo)

template returnOnErr(res: JitResult, config: ConfigRef, node: PNode): VmFunctionPtr =
  ## Unpacks the vmgen result. If the result represents an error, exits the
  ## calling function by returning a new `nkError` wrapping `node`
  let r = res
  if r.isOk:
    r.take
  else:
    let
      vmGenDiag = r.takeErr
      diag = PAstDiag(
              kind: adVmGenError,
              location: vmGenDiag.location,
              instLoc: vmGenDiag.instLoc,
              vmGenErr: vmGenDiagToAstDiagVmGenError(vmGenDiag),
              duringJit: false)

    return config.newError(node, diag, instLoc())

proc reportIfError(config: ConfigRef, n: PNode) =
  ## If `n` is a `nkError`, reports the error via `handleReport`. This is
  ## only meant for errors from vm/vmgen invocations and is also only a
  ## transition helper until all vm invocation functions properly propagate
  ## `nkError`
  if n.isError:
    # Errors from direct vmgen invocations don't have a stack-trace
    if n.diag.kind == adVmGenError and n.diag.duringJit or
        n.diag.kind == adVmError:
      let st =
        case n.diag.kind
        of adVmGenError: n.diag.vmGenTrace
        of adVmError:    n.diag.vmTrace
        else:            unreachable()

      config.handleReport(
                wrap(VMReport(kind: rvmStackTrace,
                        currentExceptionA: st.currentExceptionA,
                        currentExceptionB: st.currentExceptionB,
                        stacktrace: st.stacktrace,
                        skipped: st.skipped,
                        location: some st.location,
                        reportInst: toReportLineInfo(st.instLoc))),
                instLoc(-1))

    config.localReport(n)


proc evalStmt(jit: var JitState, c: var TCtx, iface: CompilerIface, n: PNode): PNode =
  let n = transformExpr(jit.graph, jit.idgen, jit.module, n)
  let prc = genStmt(jit, c, n).returnOnErr(jit.config, n)

  if prc.isNil:
    result = jit.graph.emptyNode
  else:
    result = execute(jit, c, iface, prc.toFuncIndex).unpackResult(jit.config, n)

proc registerAdditionalOps*(jit: var JitState, c: var TCtx,
                            disallowDangerous: bool) =
  ## Convenience proc used for setting up the overrides relevant during
  ## compile-time execution. If `disallowDangerous` is set to 'true', all
  ## operations that are able to modify the host's environment are replaced
  ## with no-ops
  template register(list: untyped) =
    for it in list:
      registerCallback(jit, c, it.pattern, it.prc)

  register(): basicOps()
  register(): macroOps()
  register(): debugOps()
  register(): compileTimeOps()
  register(): ioReadOps()
  register(): osOps()
  register(): macroapiOps()

  let cbStart = c.callbacks.len # remember where the callbacks for dangerous
                                # ops start
  register(): gorgeOps()
  register(): ioWriteOps()
  register(): os2Ops()

  if disallowDangerous:
    # note: replacing the callbacks like this only works because
    # ``registerCallback`` always appends them to the list
    for i in cbStart..<c.callbacks.len:
      # replace with a no-op
      c.callbacks[i] = nil#proc(a: VmArgs) {.nimcall.} = discard

  # the `cpuTime` callback doesn't fit any other category so it's registered
  # here
  if optBenchmarkVM in jit.config.globalOptions or not disallowDangerous:
    registerCallback jit, c, "stdlib.times.cpuTime", proc(a: var VmEnv, b: openArray[StackValue], c: RootRef): (CallbackExitCode, StackValue) {.raises: [].} =
      result = (cecValue, cast[StackValue](cpuTime()))
  else:
    registerCallback jit, c, "stdlib.times.cpuTime",  proc(a: var VmEnv, b: openArray[StackValue], c: RootRef): (CallbackExitCode, StackValue) {.raises: [].} =
      result = (cecValue, cast[StackValue](5.391245e-44))  # Randomly chosen

proc setupGlobalCtx*(module: PSym; graph: ModuleGraph; idgen: IdGenerator) =
  addInNimDebugUtils(graph.config, "setupGlobalCtx")
  if graph.vm.isNil:
    let
      disallowDangerous =
        defined(nimsuggest) or graph.config.cmd == cmdCheck or
        vmopsDanger notin graph.config.features

    var jit = initJit(graph)
    var ctx = initCtx(legacyReportsVmTracer)
    jit.flags = {cgfAllowMeta}
    registerAdditionalOps(jit, ctx, disallowDangerous)

    graph.vm = PEvalContext(vm: ctx, jit: jit)
  elif graph.vm of PDelayedVm:
    # take the VM instance provided by the wrapper and create a proper
    # evaluation context from it
    let setup = PDelayedVm(graph.vm)
    var jit = initJit(graph)
    var ctx = initCtx(legacyReportsVmTracer)
    jit.flags = setup.flags
    jit.mode = setup.mode
    graph.vm = PEvalContext(vm: ctx, jit: jit)

  let c = PEvalContext(graph.vm)
  if c.iface.isNil:
    c.iface = CompilerIface(graph: graph, config: graph.config, cache: graph.cache)
    c.iface.nodes = addr c.jit.env.asts # XXX: ugly, but simple

  # update the JIT's module context:
  c.jit.module = module
  c.jit.idgen = idgen
  # update the interface
  c.iface.module = module
  c.iface.idgen = idgen

proc eval(jit: var JitState, c: var TCtx; iface: CompilerIface, prc: PSym, n: PNode): PNode =
  let
    n = transformExpr(jit.graph, jit.idgen, jit.module, n)
    requiresValue = jit.mode != emStaticStmt
    r =
      if requiresValue: genExpr(jit, c, n)
      else:             genStmt(jit, c, n)

  let prc = r.returnOnErr(jit.config, n)
  if prc.isNil:
    return newNodeI(nkEmpty, n.info)

  logBytecode(jit.config, c, prc.toFuncIndex)

  let thread = initVmThread(c, prc.toFuncIndex, @[])
  result = execute(jit, c, iface, thread, n.typ, n.info).unpackResult(jit.config, n)

proc evalConstExprAux(module: PSym, idgen: IdGenerator, g: ModuleGraph,
                      prc: PSym, n: PNode,
                      mode: TEvalMode): PNode =
  addInNimDebugUtils(g.config, "evalConstExprAux", prc, n, result)
  setupGlobalCtx(module, g, idgen)

  # check whether the code accesses unavailable locations:
  if (let r = check(n); r != nil):
    # it does
    return g.config.newError(r, PAstDiag(kind: adSemUnavailableLocation))

  let
    c = PEvalContext(g.vm)
    oldMode = c.jit.mode

  # update the mode, and restore it once we're done
  c.jit.mode = mode
  result = eval(c.jit, c.vm, c.iface, prc, n)
  c.jit.mode = oldMode

proc evalConstExpr*(module: PSym; idgen: IdGenerator; g: ModuleGraph; e: PNode): PNode {.inline.} =
  result = evalConstExprAux(module, idgen, g, nil, e, emConst)

proc evalStaticExpr*(module: PSym; idgen: IdGenerator; g: ModuleGraph; e: PNode, prc: PSym): PNode {.inline.} =
  result = evalConstExprAux(module, idgen, g, prc, e, emStaticExpr)

proc evalStaticStmt*(module: PSym; idgen: IdGenerator; g: ModuleGraph; e: PNode, prc: PSym): PNode {.inline.} =
  result = evalConstExprAux(module, idgen, g, prc, e, emStaticStmt)

proc setupCompileTimeVar*(module: PSym; idgen: IdGenerator; g: ModuleGraph; n: PNode) {.inline.} =
  let r = evalConstExprAux(module, idgen, g, nil, n, emStaticStmt)
  # TODO: the node needs to be returned to the caller instead
  reportIfError(g.config, r)

proc setupMacroParam(jit: var JitState, c: var TCtx, x: PNode, typ: VmTypeId, formal: PType): StackValue =
  case formal.kind
  of tyStatic:
    putIntoReg(jit, c, x, typ, formal)
  else:
    var n = x
    if n.kind in {nkHiddenSubConv, nkHiddenStdConv}: n = n[1]
    # TODO: is anyone on the callsite dependent on this modifiction of `x`?
    n.typ = x.typ
    cast[StackValue](c.allocator.register(n))

proc evalMacroCall*(jit: var JitState, c: var TCtx, iface: CompilerIface, call, args: PNode,
                    sym: PSym): PNode =
  ## Evaluates a call to the macro `sym` with arguments `arg` with the VM.
  ##
  ## `call` is the original call expression, which is used as the ``wrongNode``
  ## in case of an error, as the node returned by the ``callsite`` macro API
  ## procedure, and for providing line information.
  let oldMode = jit.mode
  jit.mode = emStaticStmt
  # iface.comesFromHeuristic.line = 0'u16
  # iface.callsite = call

  defer:
    # restore the previous state when exiting this procedure
    # TODO: neither ``mode`` nor ``callsite`` should be stored as part of the
    #       global execution environment (i.e. ``TCtx``). ``callsite`` is part
    #       of the state that makes up a single VM invocation, and ``mode`` is
    #       only needed for ``vmgen``
    jit.mode = oldMode
    # iface.callsite = nil

  let wasAvailable = isAvailable(jit, c, sym)
  let prc = loadProc(jit, c, sym).returnOnErr(jit.config, call).toFuncIndex

  # make sure to only output the code listing once:
  if not wasAvailable:
    logBytecode(jit.config, c, prc)

  var stack: seq[StackValue]
  var arg = 0

  # put the normal arguments into registers
  for i in 1..<sym.typ.len:
    stack.add setupMacroParam(jit, c, args[i - 1], c.types.param(c.procs[prc.int].typ, arg), sym.typ[i])
    inc arg

  # put the generic arguments into registers
  let gp = sym.ast[genericParamsPos]
  for i in 0..<gp.safeLen:
    # skip implicit type parameters -- they're not part of the internal
    # signature
    if tfImplicitTypeParam notin gp[i].sym.typ.flags:
      let idx = sym.typ.len + i
      stack.add setupMacroParam(jit, c, args[idx - 1], c.types.param(c.procs[prc.int].typ, arg), gp[i].sym.typ)
      inc arg

  var thread = initVmThread(c, prc, stack)
  result = execute(jit, c, iface, thread, sym.internal[0], call.info).unpackResult(jit.config, call)

  if result.kind != nkError and cyclicTree(result):
    result = jit.config.newError(call, PAstDiag(kind: adCyclicTree))

proc evalMacroCall*(module: PSym; idgen: IdGenerator; g: ModuleGraph;
                    templInstCounter: ref int;
                    call, args: PNode, sym: PSym): PNode =
  ## Similar to the other ``evalMacroCall`` overload, but also updates the
  ## compile-time execution context with the provided `module`, `idgen`, `g`,
  ## and `templInstCounter`.
  setupGlobalCtx(module, g, idgen)
  let c = PEvalContext(g.vm)
  c.iface.templInstCounter = templInstCounter

  result = evalMacroCall(c.jit, c.vm, c.iface, call, args, sym)

proc dumpVmProfilerData*(graph: ModuleGraph): string =
  ## Dumps the profiler data collected by the profiler of the VM instance
  ## associated with `graph` to a string.
  let c = PEvalContext(graph.vm)
  missing("profiler")
  result = ""
    # if c != nil: dump(graph.config, c.vm.profiler)
    # else:        ""

# ----------- the VM-related compilerapi -----------

# NOTE: it might make sense to move the VM-related compilerapi into
#       ``nimeval.nim`` -- the compiler itself doesn't depend on or uses it

proc execProc*(jit: var JitState, c: var TCtx; sym: PSym;
               args: openArray[PNode]): PNode =
  # XXX: `localReport` is still used here since execProc is only used by the
  # VM's compilerapi (`nimeval`) whose users don't know about nkError yet
  if sym.kind in routineKinds:
    if sym.typ.len-1 != args.len:
      localReport(jit.config, sym.info, SemReport(
        kind: rsemWrongNumberOfArguments,
        sym: sym,
        countMismatch: (
          expected: sym.typ.len - 1,
          got: args.len)))

    else:
      let prc = block:
        # XXX: `returnOnErr` should be used here instead, but isn't for
        #      backwards compatiblity
        let r = loadProc(jit, c, sym)
        if unlikely(r.isErr):
          localReport(jit.config, vmGenDiagToLegacyVmReport(r.takeErr))
          return nil
        r.unsafeGet

      # TODO: return type handling doesn't work. But really, who cares? The
      #       compiler API is barely useable anyways :D
      var operands: seq[StackValue]

      let typ = if sym.kind == skMacro: sym.internal else: sym.typ

      # push the arguments to the stack:
      for i in 1..<typ.len:
        operands.add putIntoReg(jit, c, args[i-1], c.types.param(c.procs[prc.int].typ, i-1), typ[i])

      let thread = initVmThread(c, FunctionIndex prc, operands)
      # XXX: compiler interface instance is missing
      let r = execute(jit, c, nil, thread, typ[0], unknownLineInfo)
      result = r.unpackResult(jit.config, jit.graph.emptyNode)
      reportIfError(jit.config, result)
      if result.isError:
        result = nil

  else:
    jit.config.internalError(sym.info, "symbol doesn't represent a routine")

# XXX: the compilerapi regarding globals (getGlobalValue/setGlobalValue)
#      doesn't work the same as before. Previously, the returned PNode
#      could be used to modify the actual global value, but this is not
#      possible anymore

proc getGlobalValue*(c: EvalContext, s: PSym): PNode =
  ## Does not perform type checking, so ensure that `s.typ` matches the
  ## global's type
  internalAssert(c.jit.config, s.kind in {skLet, skVar} and sfGlobal in s.flags)
  let slot = c.vm.globals[0][c.jit.getGlobal(s)]

  result = c.vm.deserialize(c.jit.config, c.vm.allocator.translate(VirtualAddr(slot.val)), slot.typ, s.typ, s.info)

proc setGlobalValue*(c: var EvalContext; s: PSym, val: PNode) =
  ## Does not do type checking so ensure the `val` matches the `s.typ`
  internalAssert(c.jit.config, s.kind in {skLet, skVar} and sfGlobal in s.flags)
  let
    slot = c.vm.globals[0][c.jit.getGlobal(s)]
    data = constDataToMir(c.vm, c.jit, val)

  initFromExpr(c.vm.allocator.translate(VirtualAddr(slot.val)), slot.typ, data, c.jit.env, c.jit.config, c.vm)

## what follows is an implementation of the ``passes`` interface that evaluates
## the code directly inside the VM. It is used for NimScript execution and by
## the ``nimeval`` interface

proc myOpen(graph: ModuleGraph; module: PSym; idgen: IdGenerator): PPassContext {.nosinks.} =
  result = PEvalPassContext(idgen: idgen, graph: graph, module: module)

proc isDecl(n: PNode): bool =
  case n.kind
  of nkStmtList:
    # if one sub-node is not declarative, neither is `n`
    for it in n.items:
      if not isDecl(it):
        return false
    result = true
  of nkEmpty, nkTypeSection, nkConstSection, nkImportStmt, nkImportAs,
     nkImportExceptStmt, nkFromStmt, nkCommentStmt, routineDefs:
    result = true
  else:
    result = false

proc myProcess(c: PPassContext, n: PNode): PNode =
  let c = PEvalPassContext(c)
  # don't eval errornous code. Also skip declarative nodes, as those represent
  # type definitions required for bootstrapping the basic type environment
  if c.oldErrorCount == c.graph.config.errorCounter and not n.isError and
     not isDecl(n):
    setupGlobalCtx(c.module, c.graph, c.idgen)
    let eval = PEvalContext(c.graph.vm)

    let r = evalStmt(eval.jit, eval.vm, eval.iface, n)
    reportIfError(c.graph.config, r)
    # TODO: use the node returned by evalStmt as the result and don't report
    #       the error here
    result = newNodeI(nkEmpty, n.info)
  else:
    result = n
  c.oldErrorCount = c.graph.config.errorCounter

proc myClose(graph: ModuleGraph; c: PPassContext, n: PNode): PNode =
  result = myProcess(c, n)

const evalPass* = makePass(myOpen, myProcess, myClose)

func vmEventToAstDiagVmError*(evt: VmEvent): AstDiagVmError {.inline.} =
  let kind =
    case evt.kind
    of vmEvtOpcParseExpectedExpression: adVmOpcParseExpectedExpression
    of vmEvtUserError: adVmUserError
    of vmEvtUnhandledException: adVmUnhandledException
    of vmEvtCannotCast: adVmCannotCast
    of vmEvtCannotModifyTypechecked: adVmCannotModifyTypechecked
    of vmEvtNilAccess: adVmNilAccess
    of vmEvtAccessOutOfBounds: adVmAccessOutOfBounds
    of vmEvtAccessTypeMismatch: adVmAccessTypeMismatch
    of vmEvtAccessNoLocation: adVmAccessNoLocation
    of vmEvtErrInternal: adVmErrInternal
    of vmEvtIndexError: adVmIndexError
    of vmEvtOutOfRange: adVmOutOfRange
    of vmEvtOverOrUnderflow: adVmOverOrUnderflow
    of vmEvtDivisionByConstZero: adVmDivisionByConstZero
    of vmEvtArgNodeNotASymbol: adVmArgNodeNotASymbol
    of vmEvtNodeNotASymbol: adVmNodeNotASymbol
    of vmEvtNodeNotAProcSymbol: adVmNodeNotAProcSymbol
    of vmEvtIllegalConv: adVmIllegalConv
    of vmEvtIllegalConvFromXToY: adVmIllegalConvFromXToY
    of vmEvtMissingCacheKey: adVmMissingCacheKey
    of vmEvtCacheKeyAlreadyExists: adVmCacheKeyAlreadyExists
    of vmEvtFieldNotFound: adVmFieldNotFound
    of vmEvtNotAField: adVmNotAField
    of vmEvtFieldUnavailable: adVmFieldUnavailable
    of vmEvtCannotCreateNode: adVmCannotCreateNode
    of vmEvtCannotSetChild: adVmCannotSetChild
    of vmEvtCannotAddChild: adVmCannotAddChild
    of vmEvtCannotGetChild: adVmCannotGetChild
    of vmEvtNoType: adVmNoType
    of vmEvtTooManyIterations: adVmTooManyIterations

  {.cast(uncheckedAssign).}: # discriminants on both sides lead to saddness
    result =
      case kind:
      of adVmUserError:
        AstDiagVmError(
          kind: kind,
          errLoc: evt.errLoc,
          errMsg: evt.errMsg)
      of adVmArgNodeNotASymbol:
        AstDiagVmError(
          kind: kind,
          callName: evt.callName,
          argAst: evt.argAst,
          argPos: evt.argPos)
      of adVmCannotCast, adVmIllegalConvFromXToY:
        AstDiagVmError(
          kind: kind,
          formalType: evt.typeMismatch.formalType,
          actualType: evt.typeMismatch.actualType)
      of adVmIndexError:
        AstDiagVmError(
          kind: kind,
          indexSpec: evt.indexSpec)
      of adVmErrInternal, adVmNilAccess, adVmIllegalConv,
          adVmFieldUnavailable, adVmFieldNotFound,
          adVmCacheKeyAlreadyExists, adVmMissingCacheKey,
          adVmCannotCreateNode:
        AstDiagVmError(
          kind: kind,
          msg: evt.msg)
      of adVmCannotSetChild, adVmCannotAddChild, adVmCannotGetChild,
          adVmNoType, adVmNodeNotASymbol:
        AstDiagVmError(
          kind: kind,
          ast: evt.ast)
      of adVmUnhandledException:
        AstDiagVmError(
          kind: kind,
          ast: evt.exc)
      of adVmNotAField:
        AstDiagVmError(
          kind: kind,
          sym: evt.sym)
      of adVmOpcParseExpectedExpression,
          adVmCannotModifyTypechecked,
          adVmAccessOutOfBounds,
          adVmAccessTypeMismatch,
          adVmAccessNoLocation,
          adVmOutOfRange,
          adVmOverOrUnderflow,
          adVmDivisionByConstZero,
          adVmNodeNotAProcSymbol,
          adVmTooManyIterations:
        AstDiagVmError(kind: kind)