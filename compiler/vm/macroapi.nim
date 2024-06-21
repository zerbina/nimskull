## Implements the various operations from the `macros <#std/macros>`_ module.

import
  compiler/ast/[ast, idents, ast_idgen, reports_vm, report_enums, reports, renderer, trees, types],
  compiler/modules/modulegraphs,
  compiler/front/[options, msgs],
  compiler/sem/[evaltempl, sighashes],
  compiler/vm/[vmdef, vmalloc, vmconv, vmdeps],
  compiler/utils/[idioms, containers, astrepr],
  experimental/[results]

from compiler/mir/mirtrees import AstId

type
  CompilerIface* {.final.} = ref object of RootObj
    ## The compiler state the macro API implementation needs access to.
    graph*: ModuleGraph
    config*: ConfigRef
    cache*: IdentCache
    idgen*: IdGenerator
    module*: PSym

    templInstCounter*: ref int
      ## gives every template instantiation a unique ID, needed here for getAst
    vmstateDiff*: seq[(PSym, PNode)]
      ## we remember the "diff" to global state here (feature for IC)

    nodes*: ptr Store[AstId, PNode]
      ## ASTs referenced directly from code, usually through ``nkNimNodeLit``
    # XXX: it's quite tricky to get the nodes into the VM. For now, we're
    #      keeping a pointer to the ``MirEnv``'s storage here

template op(name: string, body: untyped) {.dirty.} =
  yield (name, proc (env: var VmEnv, args: openArray[StackValue], cl: RootRef): (CallbackExitCode, StackValue) {.raises: [].} =
    body
  )

template refVal(x: StackValue): ForeignRef =
  cast[ForeignRef](x)

template raiseError() =
  # TODO: implement properly
  return (cecRaise, StackValue(0))

template ret(x: untyped) =
  return (cecValue, cast[StackValue](x))

template ret(n: PNode) =
  ret env.allocator.register(n)

template error() =
  return (cecError, StackValue(0))

template get(x: StackValue): PNode =
  {.line.}:
    if unlikely(not env.allocator.check(x.refVal)):
      error()
    env.allocator.lookup(x.refVal, PNode)

template check(x: bool) =
  if unlikely(not x):
    error()

template getStr(a: VirtualAddr): string =
  var s: string
  check readString(env, a, s)
  s

iterator macroapiOps*(): tuple[pattern: string, prc: VmCallback] =
  op "system.loadNimNode":
    # only the code generator can emit calls to the load procedure, so the
    # index is known to be safe (unless there's a bug in the compiler).
    # (non-semmed) AST can be freely modified at run-time, so the tree is
    # duplicated first
    # ignore the raise effects of copyTree, they should never happen in
    # practice
    {.cast(raises: []).}:
      ret copyTree(CompilerIface(cl).nodes[][AstId(args[0].uintVal)])
  op "macros.intVal":
    let n = get(args[0])
    if n.kind in nkIntLiterals:
      ret n.intVal
    elif n.kind == nkSym and n.sym.kind == skEnumField:
      ret n.sym.position
    else:
      error() # TODO: proper error
  op "macros.intVal=":
    get(args[0]).intVal = args[1].intVal
  op "macros.floatVal":
    ret get(args[0]).floatVal
  op "macros.floatVal=":
    get(args[0]).floatVal = args[1].floatVal
  op "macros.strVal":
    let arg = get(args[1])
    var str {.cursor.}: string
    case arg.kind
    of nkSym: str = arg.sym.name.s
    of nkIdent: str = arg.ident.s
    of nkCommentStmt:
      {.cast(raises: []).}:
        check writeString(env, args[0].addrVal, arg.comment)
      return
    of nkStrKinds: str = arg.strVal
    else: error() # TODO: report a proper error

    check writeString(env, args[0].addrVal, str)
  op "macros.strVal=":
    let n = get(args[0])
    case n.kind
    of nkStrKinds:
      n.strVal = readString(env, args[1].addrVal)
    of nkCommentStmt:
      {.cast(raises: []).}:
        n.comment = readString(env, args[1].addrVal)
    else:
      error() # TODO: report a proper error
  op "macros.kind":
    ret ord(get(args[0]).kind)
  op "macros.symKind":
    # TODO: verify that the field is accessible
    ret ord(get(args[0]).sym.kind)
  op "macros.len":
    ret get(args[0]).safeLen
  op "macros.get":
    # TODO: make sure the sons field is available
    # TODO: index check
    ret get(args[0]).sons[args[1].intVal]
  op "macros.set":
    get(args[0]).sons[args[1].intVal] = get(args[2])
  op "macros.genSym":
    let cl = CompilerIface(cl)
    # TODO: properly set the info
    # TODO: validate the symbol kind
    var name = readString(env, args[1].addrVal)
    if name.len == 0:
      name = ":tmp"
    let sym = newSym(args[0].TSymKind, getIdent(cl.cache, name), nextSymId cl.idgen, cl.module.owner, env.debug[0])
    incl(sym.flags, sfGenSym)
    ret env.allocator.register(newSymNode(sym))
  op "macros.sameTree":
    if (args[0].uintVal == 0 or args[1].uintVal == 0):
      # one is nil the other is not -> not the same
      ret ord(args[0].uintVal == args[1].uintVal)
    else:
      {.cast(raises: []).}:
        ret ord(exprStructuralEquivalentStrictSymAndComm(get(args[0]), get(args[1])))
  op "macros.getFile":
    let cl = CompilerIface(cl)
    check writeString(env, args[0].addrVal, toFullPath(cl.config, get(args[1]).info))
  op "macros.getLine":
    ret get(args[0]).info.line.int
  op "macros.getColumn":
    ret get(args[0]).info.col.int
  op "macros.newNimNode":
    # TODO: fetch the line info
    # TODO: validate the node kind
    ret newNodeI(args[0].TNodeKind, env.debug[0])
  op "macros.newIdentNode":
    # TODO: fetch the line info
    # TODO: validate the node kind
    ret newIdentNode(CompilerIface(cl).cache.getIdent(getStr(args[0].addrVal)), env.debug[0])
  op "macros.copyNimNode":
    {.cast(raises: []).}:
      ret copyNode(get(args[0]))
  op "macros.copyNimTree":
    {.cast(raises: []).}:
      ret copyTree(get(args[0]))
  op "macros.sameIdent":
    # TODO: inefficient; compare the strings directly in VM memory
    ret ord(idents.cmpIgnoreStyle(getStr(args[0].addrVal), getStr(args[1].addrVal), high(int)) == 0)
  op "macros.signatureHash":
    let n = get(args[1])
    if n.kind == nkSym:
      {.cast(raises: []).}:
        check writeString(env, args[0].addrVal, $sigHash(n.sym))
    else:
      error() # TODO: proper error
  op "macros.sameType":
    {.cast(raises: []).}:
      ret ord(get(args[0]).typ.sameTypeOrNil(get(args[1]).typ, {ExactTypeDescValues, ExactGenericParams}))
  op "macros.add":
    get(args[0]).add get(args[1])
    ret args[0]
  op "macros.getImpl":
    var a = get(args[0])
    if a.kind == nkVarTy: a = a[0]
    if a.kind == nkSym:
      if a.sym.ast.isNil:
        ret StackValue(0)
      else:
        {.cast(raises: []).}:
          ret copyTree(a.sym.ast)
    else:
      error() # TODO: proper error
  op "macros.error":
    error() # TODO: proper error
  op "macros.del":
    let n = get(args[0])
    let bb = args[1].intVal
    for i in 0..<args[2].intVal:
      delSon(n, bb.int)
  op "repr_v2.renderTree": # XXX: the procedure is misplaced
    {.cast(raises: []).}:
      check writeString(env, args[0].addrVal,
        renderTree(get(args[1]), {renderNoComments, renderDocComments}))
  op "macros.getType":
    # TODO: proper line information
    let cl = CompilerIface(cl)
    let n = get(args[0])
    {.cast(raises: []).}:
      if n.typ != nil:
        ret opMapTypeToAst(cl.cache, n.typ, env.debug[0], cl.idgen)
      elif n.kind == nkSym and n.sym.typ != nil:
        ret opMapTypeToAst(cl.cache, n.sym.typ, env.debug[0], cl.idgen)
      else:
        raiseError()
      # raiseVmError(VmEvent(kind: vmEvtNoType))
  op "macros.typeKind":
    let n = get(args[0])
    if n.typ != nil:
      ret ord(n.typ.kind)
    elif n.kind == nkSym and n.sym.typ != nil:
      ret ord(n.sym.typ.kind)
    else:
      ret ord(tyNone)
  op "macros.getTypeInst":
    let n = get(args[0])
    let cl = CompilerIface(cl)
    # TODO: proper line information
    {.cast(raises: []).}:
      if n.typ != nil:
        ret opMapTypeInstToAst(cl.cache, n.typ, env.debug[0], cl.idgen)
      elif n.kind == nkSym and n.sym.typ != nil:
        ret opMapTypeInstToAst(cl.cache, n.sym.typ, env.debug[0], cl.idgen)
      else:
        raiseError()
      #raiseVmError(VmEvent(kind: vmEvtNoType))
  op "macros.getTypeImpl":
    let n = get(args[0])
    let cl = CompilerIface(cl)
    # TODO: proper line information
    {.cast(raises: []).}:
      if n.typ != nil:
        ret opMapTypeImplToAst(cl.cache, n.typ, env.debug[0], cl.idgen)
      elif n.kind == nkSym and n.sym.typ != nil:
        ret opMapTypeImplToAst(cl.cache, n.sym.typ, env.debug[0], cl.idgen)
      else:
        #raiseVmError(VmEvent(kind: vmEvtNoType))
        raiseError()
  op "macros.getAst":
    let cl = CompilerIface(cl)
    let templ = cl.nodes[][args[0].uintVal.AstId]
    # TODO: pick the correct owner
    let genSymOwner = cl.module
    # TODO: use proper line information
    var templCall = newNodeI(nkCall, env.debug[0], args.len)
    templCall[0] = templ
    for i in 1..<args.len:
      templCall[i] = get(args[i])

    {.cast(raises: []).}:
      var a = evalTemplate(templCall, templ.sym, genSymOwner, cl.config, cl.cache,
                          cl.templInstCounter, cl.idgen)
      if a.kind == nkStmtList and a.len == 1: # flatten if a single statement
        a = a[0]

    ret a
  op "macros.internalParseExpr":
    let cl = CompilerIface(cl)
    # TODO: proper line info is missing
    {.cast(raises: []).}:
      # in theory, parseCode can raise an IOError, in practice it doesn't
      var parsed = parseCode(getStr(args[0].addrVal), cl.cache, cl.config, env.debug[0])

    type Res = typeof(parsed)

    # make sure that the parsed code is that of an expression:
    parsed = parsed.flatMap proc(ast: PNode): Res =
      if ast.len == 1:
        assert ast.kind == nkStmtList
        Res.ok:  ast[0]
      else:
        Res.err: VMReport(kind: rvmOpcParseExpectedExpression).wrap()

    if parsed.isOk:
      # success! Write the parsed AST to the result register and return an
      # empty error message
      ret parsed.unsafeGet
    else:
      # failure. Write the error message to the string
      {.cast(raises: []).}:
        check writeString(env, args[1].addrVal, errorReportToString(cl.config, parsed.error))
      ret nil
