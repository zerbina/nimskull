
import compiler/ast/[ast_types, idents, lineinfos, ast_idgen, ast, types, trees]
import compiler/sem/[lowerings, closureiters]
import compiler/modules/[modulegraphs, magicsys]
import compiler/utils/[idioms]

type RewriteCtx = object
  owner: PSym
  param: PSym
  resultVar: PSym
  realType: PType
  selfSym: PSym

  graph: ModuleGraph
  cache: IdentCache
  idgen: IdGenerator

proc getCoroType(s: PSym): PType =
  ## Returns the concrete internal type of a coroutine.
  assert sfCoroutine in s.flags
  s.ast[dispatcherPos].sym.ast[dispatcherPos].typ

proc newTemp(c: RewriteCtx, typ: PType, info: TLineInfo): PSym =
  let r = newSym(skTemp, getIdent(c.cache, ":tmp"), nextSymId(c.idgen), c.owner, info)
  r.typ = typ
  r

proc contAccess(c: RewriteCtx, info: TLineInfo): PNode =
  newTreeIT(nkObjDownConv, info, c.realType, newSymNode(c.param))

proc genPostCoro*(graph: ModuleGraph, callee: PSym, n: PNode, coro: PNode) =
  n.add newTreeI(nkCall, n.info, newSymNode graph.getCompilerProc("nimCheckCoro"), coro)
  if not callee.typ[0].isEmptyType():
    # read the coroutine's result
    n.transitionSonsKind(nkStmtListExpr)
    # TODO: this needs to move instead of copy
    n.add indirectAccess(copyTree(coro), callee.ast[resultPos].sym.itemId, n.info)

proc callToCoroSetup*(graph: ModuleGraph, call: PNode; expect: PType, parent: PNode = nil): PNode =
  let cont = getCoroType(call[0].sym)
  result = newTreeIT(nkObjConstr, call.info, cont, newNodeIT(nkType, call.info, cont))
  result.add newTree(nkExprColonExpr, newSymNode graph.getCompilerProc("Coroutine").typ.base.n[1].sym, newSymNode call[0].sym.ast[dispatcherPos].sym)
  if parent != nil:
    result.add newTree(nkExprColonExpr, newSymNode graph.getCompilerProc("Coroutine").typ.base.n[3].sym, parent)
  # setup the parameter values in the coroutine object with the arguments
  for i in 1..<call.len:
    result.add newTree(nkExprColonExpr, newSymNode getFieldFromObj(cont.base, call[0].typ.n[i].sym), call[i])
  # up-convert to the expected type:
  result = newTreeIT(nkObjUpConv, call.info, expect, result)

proc genResultAsgn(c: RewriteCtx, info: TLineInfo): PNode =
  # return the parent when exiting the coroutine
  newTreeI(nkAsgn, info,
    newSymNode(c.resultVar),
    newTreeIT(nkCall, info, c.resultVar.typ, newSymNode(c.graph.getCompilerProc("nimReturn")), newSymNode(c.param)))

proc rewrite(c: RewriteCtx, n: PNode): PNode =
  case n.kind
  of nkWithoutSons - {nkSym}:
    result = n
  of nkSym:
    if n.sym.id == c.selfSym.id:
      # replace the ``self`` symbol with a down-coverted parameter access
      result = newTreeIT(nkObjDownConv, n.info, c.selfSym.typ, newSymNode c.param)
    elif n.sym.kind in skLocalVars and sfGlobal notin n.sym.flags:
      # lift all fields
      let field = addUniqueField(c.realType.base, n.sym, c.cache, c.idgen)
      result = newTreeIT(nkDotExpr, n.info, field.typ, newTreeIT(nkHiddenDeref, n.info, c.realType.base, contAccess(c, n.info)), newSymNode field)
    else:
      result = n
  of nkReturnStmt:
    # when returning from a coroutine, the actual result is stored within the
    # coroutine object, and the next coroutine is returned
    result = newTreeI(nkStmtList, n.info,
      newTreeI(nkAsgn, n.info, indirectAccess(contAccess(c, n.info), n[0][0].sym, n.info)),
      newTreeI(nkReturnStmt, n.info, genResultAsgn(c, n.info))
    )
  of nkCallKinds:
    for i in 0..<n.len:
      let tmp = rewrite(c, n[i])
      n[i] = tmp

    if getMagic(n) == mCps:
      # continuation passing: pass the current coroutine to the
      # procedure. The procedure then returns what to continue with
      n[1].sons.insert(newTreeIT(nkObjDownConv, n.info, n[1][0].sym.typ[1], newSymNode(c.param)), 1)
      result = newTreeI(nkYieldStmt, n.info, newTreeIT(nkObjUpConv, n.info, c.param.typ, n[1]))
    elif n[0].kind == nkSym and sfCoroutine in n[0].sym.flags:
      # calling a coroutine within a coroutine automatically turns it into a tail call
      let callee = n[0].sym
      let cont = getCoroType(n[0].sym)
      let constr = callToCoroSetup(c.graph, n, cont, newSymNode(c.param))

      let tmp = newTemp(c, cont, n.info)
      addField(c.realType.base, tmp, c.cache, c.idgen)
      let acc = indirectAccess(contAccess(c, n.info), tmp, n.info)
      result = newTree(nkStmtList,
        newTree(nkAsgn, acc, constr),
        newTreeI(nkYieldStmt, n.info, newTreeIT(nkObjUpConv, n.info, c.param.typ, acc))
      )
      genPostCoro(c.graph, callee, result, acc)

    else:
      # nothing to do
      result = n
  else:
    for i in 0..<n.len:
      n[i] = rewrite(c, n[i])
    result = n

proc computeFieldStart(t: PType, pos: var int) =
  proc aux(n: PNode, p: var int) =
    case n.kind
    of nkRecCase:
      inc p # discriminator
      for i in 1..<n.len:
        aux(n[i], p)
    of nkRecList:
      for it in n.items:
        aux(it, p)
    of nkSym:
      inc p
    else:
      unreachable()

  let t = t.skipTypes(skipPtrs)
  assert t.kind == tyObject
  if t.len > 0 and t.base != nil:
    computeFieldStart(t.base, pos)

  aux(t.n, pos)

proc transformCoroBody*(graph: ModuleGraph, idgen: IdGenerator, sym: PSym, n: PNode): PNode =

  let
    selfSym = sym.ast[dispatcherPos].sym
    base = selfSym.typ

  var obj = createObj(graph, idgen, sym, n.info, final=true)
  obj[0] = base
  propagateToOwner(obj, obj.base)
  let re = newType(tyRef, nextTypeId idgen, sym)
  re.rawAddSon(obj)

  let coro = newSym(skProc, sym.name, nextSymId idgen, sym, n.info)
  coro.typ = newProcType(n.info, nextTypeId idgen, sym)
  coro.typ.callConv = ccNimCall
  let param = newSym(skParam, graph.cache.getIdent(":envP"), nextSymId idgen, coro, n.info)
  param.typ = graph.getCompilerProc("Coroutine").typ
  param.flags.incl sfFromGeneric

  coro.typ[0] = graph.getCompilerProc("Coroutine").typ
  coro.typ.rawAddSon(param.typ)
  coro.typ.n.add newSymNode(param)

  coro.ast = newProcNode(nkProcDef, n.info, n, nkFormalParams.newTree(newNodeIT(nkType, n.info, coro.typ[0]), newSymNode param), newSymNode coro, graph.emptyNode, graph.emptyNode, graph.emptyNode, graph.emptyNode)
  coro.ast.sons.setLen(dispatcherPos + 1)
  coro.ast[resultPos] = newSymNode(newSym(skResult, graph.cache.getIdent("result"), nextSymId idgen, sym, n.info))
  coro.ast[resultPos].sym.typ = coro.typ[0]
  # in the dispatcher slot of the *coroutine* symbol, we store the full coroutine type
  coro.ast[dispatcherPos] = newNodeIT(nkType, n.info, re)

  sym.ast[dispatcherPos] = newSymNode(coro)

  for i in 1..<sym.ast[paramsPos].len:
    addField(obj, sym.typ.n[i].sym, graph.cache, idgen)

  if not sym.typ[0].isEmptyType():
    addField(obj, sym.ast[resultPos].sym, graph.cache, idgen)

  var c = RewriteCtx(graph: graph, idgen: idgen, cache: graph.cache, owner: coro, selfSym: selfSym, resultVar: coro.ast[resultPos].sym, realType: re, param: coro.ast[paramsPos][1].sym)
  # the closure iterato transformation does the main work
  let b = newTree(nkStmtList,
    rewrite(c, n),
    genResultAsgn(c, n.info))

  let body = transformClosureIterator(graph, idgen, coro, b)
  # wrap the body in a try-except block, so that no exception escapes:
  # TODO: only do this when the body actually raises an exception
  # TODO: only handle catchable errors
  let get = c.graph.getCompilerProc("getCurrentException")
  let exc = newTree(nkStmtList,
    newTree(nkAsgn, indirectAccess(newSymNode(c.param), "error", n.info, c.cache), newTreeIT(nkCall, n.info, get.typ[0], newSymNode get))
  )
  result = newTreeI(nkTryStmt, body.info, body, newTree(nkExceptBranch, exc))
  coro.ast[bodyPos] = result

  # patch the field positions, they're wrong
  var pos: int
  computeFieldStart(obj.base, pos)
  for i in 0..<obj.n.len:
    obj.n[i].sym.position += pos
