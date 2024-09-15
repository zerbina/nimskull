import
  std/[
    intsets
  ],
  compiler/ast/[
    ast,
    renderer,
    types
  ],
  compiler/front/[
    options, msgs
  ]

from compiler/ast/reports_sem import SemReport
import compiler/ast/report_enums

import std/private/asciitables

# note: large parts of this module are copied from ``dfa.nim``

type
  InstrKind* = enum
    goto, loop, fork
    def, use, mut, kill, borrow
    call
  Instr* = object
    n*: PNode ## contains the def/use/mut
    case kind: InstrKind
    of goto, loop, fork:
      dest*: int
    of borrow:
      borrower: PNode
    else:
      discard

  ControlFlowGraph* = seq[Instr]

  TPosition = distinct int

  TBlock = object
    vars: int
    case isTryBlock: bool
    of false:
      label: PSym
      breakFixups: seq[(TPosition, seq[PNode])] #Contains the gotos for the breaks along with their pending finales
    of true:
      finale: PNode
      raiseFixups: seq[TPosition] #Contains the gotos for the raises

  Con = object
    config: ConfigRef
    code: ControlFlowGraph
    inTryStmt: int
    vars: seq[PNode] ## all variable with currently live storage
    blocks: seq[TBlock]
    owner: PSym
    borrowCtx: PNode

proc codeListing(c: ControlFlowGraph, start = 0; last = -1): string =
  # for debugging purposes
  # first iteration: compute all necessary labels:
  var jumpTargets = initIntSet()
  let last = if last < 0: c.len-1 else: min(last, c.len-1)
  for i in start..last:
    if c[i].kind in {goto, fork, loop}:
      jumpTargets.incl(c[i].dest)
  var i = start
  while i <= last:
    if i in jumpTargets: result.add("L" & $i & ":\n")
    result.add "\t"
    result.add ($i & " " & $c[i].kind)
    result.add "\t"
    case c[i].kind
    of def, use, mut, kill, borrow, call:
      result.add renderTree(c[i].n)
    of goto, fork, loop:
      result.add "L"
      result.addInt c[i].dest
    result.add("\t#")
    result.add($c[i].n.info.line)
    result.add("\n")
    inc i
  if i in jumpTargets: result.add("L" & $i & ": End\n")

proc echoCfg*(c: ControlFlowGraph; start = 0; last = -1) {.deprecated.} =
  ## echos the ControlFlowGraph for debugging purposes.
  echo codeListing(c, start, last).alignTable

proc forkI(c: var Con; n: PNode): TPosition =
  result = TPosition(c.code.len)
  c.code.add Instr(n: n, kind: fork, dest: 0)

proc gotoI(c: var Con; n: PNode): TPosition =
  result = TPosition(c.code.len)
  c.code.add Instr(n: n, kind: goto, dest: 0)

proc loopI(c: var Con; n: PNode, dest: TPosition) =
  c.code.add Instr(n: n, kind: loop, dest: dest.int)

proc genLabel(c: Con): TPosition = TPosition(c.code.len)

proc patch(c: var Con, p: TPosition) =
  # patch with current index
  c.code[p.int].dest = c.code.len

proc gen(c: var Con; n: PNode)

proc popBlock(c: var Con; oldLen: int) =
  var exits: seq[TPosition]
  exits.add c.gotoI(newNode(nkEmpty))
  for f in c.blocks[oldLen].breakFixups:
    c.patch(f[0])
    for finale in f[1]:
      c.gen(finale)
    exits.add c.gotoI(newNode(nkEmpty))
  for e in exits:
    c.patch e

  c.vars.setLen(c.blocks[oldLen].vars)
  c.blocks.setLen(oldLen)

template withBlock(labl: PSym; body: untyped) =
  let oldLen = c.blocks.len
  c.blocks.add TBlock(isTryBlock: false, label: labl, vars: c.vars.len)
  body
  popBlock(c, oldLen)

proc popScope(c: var Con, to: int) =
  for i in to ..< c.vars.len:
    c.code.add Instr(n: c.vars[i], kind: kill)
  c.vars.setLen(to)

template withScope(body: untyped) =
  let vars = c.vars.len
  body
  popScope(c, vars)

proc isTrue(n: PNode): bool =
  n.kind == nkSym and n.sym.kind == skEnumField and n.sym.position != 0 or
    n.kind == nkIntLit and n.intVal != 0

template forkT(n, body) =
  let lab1 = c.forkI(n)
  body
  c.patch(lab1)

proc genWhile(c: var Con; n: PNode) =
  # lab1:
  #   cond, tmp
  #   fork tmp, lab2
  #   body
  #   loop lab1
  # lab2:
  let lab1 = c.genLabel
  withBlock(nil):
    withScope:
      if isTrue(n[0]):
        c.gen(n[1])
        c.loopI(n, lab1)
      else:
        c.gen(n[0])
        forkT(n):
          c.gen(n[1])
          c.loopI(n, lab1)

proc genIf(c: var Con, n: PNode) =
  #[

  if cond:
    A
  elif condB:
    B
  elif condC:
    C
  else:
    D

  cond
  fork lab1
  A
  goto Lend
  lab1:
    condB
    fork lab2
    B
    goto Lend2
  lab2:
    condC
    fork L3
    C
    goto Lend3
  L3:
    D
    goto Lend3 # not eliminated to simplify the join generation
  Lend3:
    join F3
  Lend2:
    join F2
  Lend:
    join F1

  ]#
  var endings: seq[TPosition] = @[]
  for i in 0..<n.len:
    let it = n[i]
    let scope = c.vars.len
    c.gen(it[0])
    if it.len == 2:
      forkT(it[1]):
        c.gen(it[1])
        c.popScope(scope)
        endings.add c.gotoI(it[1])
    else:
      c.popScope(scope)

  for i in countdown(endings.high, 0):
    c.patch(endings[i])

proc genAndOr(c: var Con; n: PNode) =
  #   asgn dest, a
  #   fork lab1
  #   asgn dest, b
  # lab1:
  #   join F1
  c.gen(n[1])
  forkT(n):
    c.gen(n[2])

proc genCase(c: var Con; n: PNode) =
  #  if (!expr1) goto lab1;
  #    thenPart
  #    goto LEnd
  #  lab1:
  #  if (!expr2) goto lab2;
  #    thenPart2
  #    goto LEnd
  #  lab2:
  #    elsePart
  #  Lend:
  let isExhaustive = skipTypes(n[0].typ,
    abstractVarRange-{tyTypeDesc}).kind notin {tyFloat..tyFloat64, tyString}

  # we generate endings as a set of chained gotos, this is a bit awkward but it
  # ensures when recursively traversing the CFG for various analysis, we don't
  # artificially extended the life of each branch (for the purposes of DFA)
  # beyond the minimum amount.
  var endings: seq[TPosition] = @[]
  c.gen(n[0])
  # TODO: add scope handling
  for i in 1..<n.len:
    let it = n[i]
    if it.len == 1 or (i == n.len-1 and isExhaustive):
      # treat the last branch as 'else' if this is an exhaustive case statement.
      c.gen(it.lastSon)
      if endings.len != 0:
        c.patch(endings[^1])
    else:
      forkT(it.lastSon):
        c.gen(it.lastSon)
        if endings.len != 0:
          c.patch(endings[^1])
        endings.add c.gotoI(it.lastSon)

proc genBlock(c: var Con; n: PNode) =
  withBlock(n[0].sym):
    c.gen(n[1])

proc genBreakOrRaiseAux(c: var Con, i: int, n: PNode) =
  for v in c.blocks[i].vars ..< c.vars.len:
    c.code.add Instr(n: c.vars[v], kind: kill)

  let lab1 = c.gotoI(n)
  if c.blocks[i].isTryBlock:
    c.blocks[i].raiseFixups.add lab1
  else:
    var trailingFinales: seq[PNode]
    if c.inTryStmt > 0: #Ok, we are in a try, lets see which (if any) try's we break out from:
      for b in countdown(c.blocks.high, i):
        if c.blocks[b].isTryBlock:
          trailingFinales.add c.blocks[b].finale

    c.blocks[i].breakFixups.add (lab1, trailingFinales)

proc genBreak(c: var Con; n: PNode) =
  if n[0].kind == nkSym:
    for i in countdown(c.blocks.high, 0):
      if not c.blocks[i].isTryBlock and c.blocks[i].label == n[0].sym:
        genBreakOrRaiseAux(c, i, n)
        return
    #globalError(n.info, "VM problem: cannot find 'break' target")
  else:
    for i in countdown(c.blocks.high, 0):
      if not c.blocks[i].isTryBlock:
        genBreakOrRaiseAux(c, i, n)
        return

proc genTry(c: var Con; n: PNode) =
  var endings: seq[TPosition] = @[]

  let oldLen = c.blocks.len
  c.blocks.add TBlock(isTryBlock: true, finale: if n[^1].kind == nkFinally: n[^1] else: newNode(nkEmpty))

  inc c.inTryStmt
  c.gen(n[0])
  dec c.inTryStmt

  for f in c.blocks[oldLen].raiseFixups:
    c.patch(f)

  c.blocks.setLen oldLen

  for i in 1..<n.len:
    let it = n[i]
    if it.kind != nkFinally:
      forkT(it):
        c.gen(it.lastSon)
        endings.add c.gotoI(it)
  for i in countdown(endings.high, 0):
    c.patch(endings[i])

  let fin = lastSon(n)
  if fin.kind == nkFinally:
    c.gen(fin[0])

template genNoReturn(c: var Con; n: PNode) =
  # leave the graph
  c.code.add Instr(n: n, kind: goto, dest: high(int) - c.code.len)

proc genRaise(c: var Con; n: PNode) =
  gen(c, n[0])
  if c.inTryStmt > 0:
    for i in countdown(c.blocks.high, 0):
      if c.blocks[i].isTryBlock:
        genBreakOrRaiseAux(c, i, n)
        return
    assert false #Unreachable
  else:
    genNoReturn(c, n)

proc genImplicitReturn(c: var Con) =
  if c.owner.kind in {skProc, skFunc, skMethod, skIterator, skConverter} and resultPos < c.owner.ast.len:
    gen(c, c.owner.ast[resultPos])

proc genReturn(c: var Con; n: PNode) =
  if n[0].kind != nkEmpty:
    gen(c, n[0])
  else:
    genImplicitReturn(c)
  genBreakOrRaiseAux(c, 0, n)

const
  InterestingSyms = {skVar, skResult, skLet, skParam, skForVar, skTemp}
  PathKinds0 = {nkDotExpr, nkCheckedFieldExpr,
                nkBracketExpr, nkHiddenDeref,
                nkObjDownConv, nkObjUpConv}
  PathKinds1 = {nkHiddenStdConv, nkHiddenSubConv}

proc skipConvDfa*(n: PNode): PNode =
  result = n
  while true:
    case result.kind
    of nkObjDownConv, nkObjUpConv:
      result = result[0]
    of PathKinds1:
      result = result[1]
    else: break

type AliasKind* = enum
  yes, no, maybe

proc aliases*(obj, field: PNode): AliasKind =
  ##[

============ =========== ====
obj          field       alias kind
------------ ----------- ----
`x`          `x`         true
`x`          `x.f`       true
`x.f`        `x`         false
`x.f`        `x.f`       true
`x.f`        `x.v`       false
`x`          `x[0]`      true
`x[0`]       `x`         false
`x[0`]       `x[0]`      true
`x[0`]       `x[1]`      false
`x`          `x[i]`      true
`x[i`]       `x`         false
`x[i`]       `x[i]`      maybe; Further analysis could make this return true when i is a runtime-constant
`x[i`]       `x[j]`      maybe; also returns maybe if only one of i or j is a compiletime-constant

============ =========== ======

  ]##

  template collectImportantNodes(result, n) =
    var result: seq[PNode]
    var n = n
    while true:
      case n.kind
      of PathKinds0 - {nkDotExpr, nkBracketExpr}:
        n = n[0]
      of PathKinds1:
        n = n[1]
      of nkDotExpr, nkBracketExpr:
        result.add n
        n = n[0]
      of nkSym:
        result.add n; break
      else: return no

  collectImportantNodes(objImportantNodes, obj)
  collectImportantNodes(fieldImportantNodes, field)

  # If field is less nested than obj, then it cannot be part of/aliased by obj
  if fieldImportantNodes.len < objImportantNodes.len: return no

  result = yes
  for i in 1..objImportantNodes.len:
    # We compare the nodes leading to the location of obj and field
    # with each other.
    # We continue until they diverge, in which case we return no, or
    # until we reach the location of obj, in which case we do not need
    # to look further, since field must be part of/aliased by obj now.
    # If we encounter an element access using an index which is a runtime value,
    # we simply return maybe instead of yes; should further nodes not diverge.
    let currFieldPath = fieldImportantNodes[^i]
    let currObjPath = objImportantNodes[^i]

    if currFieldPath.kind != currObjPath.kind:
      return no

    case currFieldPath.kind
    of nkSym:
      if currFieldPath.sym != currObjPath.sym: return no
    of nkDotExpr:
      if currFieldPath[1].sym != currObjPath[1].sym: return no
    of nkBracketExpr:
      if currFieldPath[1].kind in nkLiterals and currObjPath[1].kind in nkLiterals:
        if currFieldPath[1].intVal != currObjPath[1].intVal:
          return no
      else:
        result = maybe
    else: assert false # unreachable

proc skipTrivials(n: PNode): PNode =
  result = n
  while true:
    case result.kind
    of PathKinds0 - {nkDerefExpr, nkHiddenDeref}:
      result = result[0]
    of PathKinds1:
      result = result[1]
    else: break

proc isInteresting(c: Con, s: PSym): bool =
  s.kind in InterestingSyms

proc genUse(c: var Con; orig: PNode) =
  let n = skipTrivials(orig)

  if (n.kind == nkSym and c.isInteresting(n.sym)) or
     n.kind in {nkDerefExpr, nkHiddenDeref}:
    c.code.add Instr(n: orig, kind: use)

proc genMut(c: var Con; orig: PNode) =
  let n = skipTrivials(orig)

  if (n.kind == nkSym and c.isInteresting(n.sym)) or
     n.kind in {nkDerefExpr, nkHiddenDeref}:
    c.code.add Instr(n: orig, kind: mut)

proc genDef(c: var Con; orig: PNode) =
  var n = skipConvDfa(orig)
  if n.kind == nkSym and c.isInteresting(n.sym):
    # a direct assignemnt, e.g., ``a = b``
    c.code.add Instr(n: orig, kind: def)
    return

  n = skipTrivials(n)
  if n.kind in {nkSym, nkDerefExpr, nkHiddenDeref}:
    # an assignment to a sub-location, e.g., ``a.b = c``
    c.code.add Instr(n: orig, kind: mut)

proc isLentParameter(c: ConfigRef, param: PSym, ret: PType): bool =
  # decides whether the parameter effectively borrows the argument lvalue
  if isPassByRef(c, param, ret):
    # a pass-by-reference parameter -> no copy takes place
    true
  elif param.typ.kind == tySink:
    false # either a full copy or a move
  else:
    # if the type has a destructor, a shallow copy takes place, which is
    # effectively a borrow
    hasDestructor(param.typ)

template withContext(n: PNode, body: untyped) =
  let prev = c.borrowCtx
  c.borrowCtx = n
  body
  c.borrowCtx = prev

proc genCall(c: var Con; n: PNode) =
  gen(c, n[0])
  genUse(c, n[0])
  var t = n[0].typ
  if t != nil: t = t.skipTypes(abstractInst)
  for i in 1..<n.len:
    withContext n:
      gen(c, n[i])
    if n[i].kind != nkHiddenAddr and not isLentParameter(c.config, t.n[i].sym, t[0]):
      # used right away
      genUse(c, n[i])

    when false:
      if t != nil and i < t.len and t[i].kind == tyOut:
        # Pass by 'out' is a 'must def'. Good enough for a move optimizer.
        genDef(c, n[i])

  # values passed by reference are also used within the procedure
  for i in 1..<n.len:
    if n[i].kind != nkHiddenAddr and isLentParameter(c.config, t.n[i].sym, t[0]):
      genUse(c, n[i])

  c.code.add Instr(n: n, kind: call)
  # sequence the mutations after the call instruction, so that they don't
  # conflict with the parameter borrows

  # var parameter mutations happen *within* the called procedure
  for i in 1..<n.len:
    if n[i].kind == nkHiddenAddr:
      genMut(c, n[i][0])

  # every call can potentially raise:
  if c.inTryStmt > 0 and canRaiseConservative(n[0]):
    # we generate the instruction sequence:
    # fork lab1
    # goto exceptionHandler (except or finally)
    # lab1:
    # join F1
    forkT(n):
      for i in countdown(c.blocks.high, 0):
        if c.blocks[i].isTryBlock:
          genBreakOrRaiseAux(c, i, n)
          break

proc genMagic(c: var Con; n: PNode; m: TMagic) =
  case m
  of mAnd, mOr: c.genAndOr(n)
  of mSlice:
    gen(c, n[1])
    gen(c, n[2])
    genUse(c, n[2])
    gen(c, n[3])
    genUse(c, n[3])
    c.code.add Instr(n: n[1], kind: borrow, borrower: c.borrowCtx)
  else:
    genCall(c, n)

proc genVarSection(c: var Con; n: PNode) =
  for a in n:
    if a.kind == nkCommentStmt:
      discard
    elif a.kind == nkVarTuple:
      gen(c, a.lastSon)
      for i in 0..<a.len-2:
        c.vars.add a[i]
        genDef(c, a[i])
    else:
      withContext a[0]:
        gen(c, a.lastSon)

      c.vars.add a[0]
      if a.lastSon.kind != nkEmpty:
        genDef(c, a[0])

proc genFor(c: var Con, n: PNode) =
  # assume that the loop is run at least once
  let lab1 = c.genLabel
  withBlock nil:
    # treat the iterator invocation as happening *within* the loop
    gen(c, n[^2])
    for def in forLoopDefs(n):
      genDef(c, def)
    # TODO: views returned from the iterator need to be handled properly
    gen(c, n[^1])
    c.loopI(n, lab1)

proc gen(c: var Con; n: PNode) =
  case n.kind
  of nkSym:
    discard
  of nkCallKinds:
    if n[0].kind == nkSym:
      let s = n[0].sym
      if s.magic != mNone:
        genMagic(c, n, s.magic)
      else:
        genCall(c, n)
      if sfNoReturn in n[0].sym.flags:
        genNoReturn(c, n)
    else:
      genCall(c, n)
  of nkLiterals: discard
  of nkAsgn, nkFastAsgn:
    gen(c, n[0])
    if n[0].kind == nkSym:
      withContext n[0]:
        gen(c, n[1])
    else:
      gen(c, n[1])

    genUse(c, n[1]) # the use of the rhs happens before the def of the lhs
    genDef(c, n[0])
  of PathKinds0 - {nkBracketExpr, nkHiddenDeref, nkDerefExpr, nkHiddenAddr, nkAddr}:
    gen(c, n[0])
  of nkHiddenDeref, nkDerefExpr:
    gen(c, n[0])
    genUse(c, n[0])
  of nkAddr:
    # taking the address of a path is not a use thereof
    gen(c, n[0])
  of nkHiddenAddr:
    assert c.borrowCtx != nil
    let x =
      if n[0].kind == nkHiddenStdConv:
        n[0][1] # XXX: workaround for var openArray
      else:
        n[0]

    gen(c, x)
    c.code.add Instr(n: x, kind: borrow, borrower: c.borrowCtx)
  of nkBracketExpr:
    gen(c, n[0])
    genUse(c, n[1]) # the index operand is used
  of nkIfStmt, nkIfExpr: genIf(c, n)
  of nkWhenStmt:
    # This is "when nimvm" node. Chose the first branch.
    gen(c, n[0][1])
  of nkCaseStmt: genCase(c, n)
  of nkWhileStmt: genWhile(c, n)
  of nkBlockExpr, nkBlockStmt: genBlock(c, n)
  of nkReturnStmt: genReturn(c, n)
  of nkRaiseStmt: genRaise(c, n)
  of nkBreakStmt: genBreak(c, n)
  of nkTryStmt, nkHiddenTryStmt: genTry(c, n)
  of nkForStmt:
    genFor(c, n)
  of nkStmtList, nkStmtListExpr, nkChckRangeF, nkChckRange64, nkChckRange,
     nkBracket, nkCurly, nkPar, nkTupleConstr, nkClosure, nkObjConstr, nkYieldStmt:
    for x in n: gen(c, x)
  of nkPragmaBlock: gen(c, n.lastSon)
  of nkDiscardStmt, nkStringToCString, nkCStringToString:
    gen(c, n[0])
    genUse(c, n[0])
  of nkConv, nkCast:
    gen(c, n[1])
    genUse(c, n[1])
  of nkExprColonExpr:
    gen(c, n[1])
    if classifyViewType(n[0].sym.typ) == noView:
      genUse(c, n[1])
  of PathKinds1:
    gen(c, n[1])
    if n.typ.skipTypes(abstractVar).kind == tyOpenArray:
      c.code.add Instr(n: n[1], kind: borrow, borrower: c.borrowCtx)
    elif skipTypes(n.typ, abstractPtrs-{tyTypeDesc}).kind in {tyTuple, tyObject} or
       compareTypes(n.typ, n[1].typ, dcEqIgnoreDistinct):
      discard "an lvalue"
    else:
      genUse(c, n[1])
  of nkVarSection, nkLetSection: genVarSection(c, n)
  of nkDefer:
    # TODO: needs to be implemented
    doAssert false, "dfa construction pass requires the elimination of 'defer'"
  of nkEmpty:
    # TODO: shouldn't be possible
    discard
  of nkConstSection, nkBindStmt, nkMixinStmt, nkImportStmt, callableDefs, nkTypeSection, nkCommentStmt, nkPragma:
    discard "ignore"
  else: c.config.internalError(n.info, $n.kind)

proc constructCfg*(config: ConfigRef, s: PSym; body: PNode): ControlFlowGraph =
  ## constructs a control flow graph for ``body``.
  var c = Con(config: config, code: @[], blocks: @[], owner: s)
  withBlock(s):
    gen(c, body)
    popScope(c, 0)
    genImplicitReturn(c)

  if irDfa in config.toDebugIr or config.isDebugEnabled(irDfa, s.name.s):
    config.writeln("-- DFA: " & s.name.s)
    config.writeln(codeListing(c.code, 0, -1).alignTable)

  result = c.code

iterator traverse[T](c: ControlFlowGraph, start: int, exit: var bool, state: var T): (int, Instr) =
  var taken: IntSet
  var next: seq[tuple[pc: int, state: T]]

  template addNext(i: int) =
    var j = 0
    while j < next.len and next[j].pc < i:
      inc j
    # don't add duplicates
    if j >= next.len or next[j].pc != i:
      next.insert((i, state), j)

  var i = start

  template resume() =
    if next.len > 0:
      (i, state) = next[0]
      next.delete(0)
    else:
      break # we're done

  while i < c.len:
    case c[i].kind
    of goto:
      addNext(c[i].dest)
      (i, state) = next[0]
      next.delete(0)
    of loop:
      if not containsOrIncl(taken, c[i].dest):
        i = c[i].dest
      else:
        resume()
    of fork:
      addNext(c[i].dest)
      inc i
    of def, use, mut, kill, borrow, call:
      yield (i, c[i])
      if exit:
        resume()
        exit = false
      else:
        inc i

  exit = i >= c.len

proc gatherBorrows(n: PNode, list: var seq[PNode]) =
  case n.kind
  of nkHiddenAddr:
    list.add n[0]
  of nkTupleConstr, nkBracket:
    for it in n.items:
      gatherBorrows(it, list)
  of nkObjConstr:
    for i in 1..<n.len:
      gatherBorrows(n[i][1], list)
  else:
    discard

proc canBorrow*(n: PNode): bool =
  case n.kind
  of nkSym:
    result = n.sym.kind in {skVar, skLet, skParam, skForVar, skResult, skConst}
  of nkHiddenDeref:
    # XXX: this is all super fuzzy. It's entirely unclear what the
    #      consequences of treating a view-derefence as a path are
    result = true
  of nkDerefExpr:
    # no ref and pointer checks are implement, so their contents cannot be
    # borrowed from
    result = false
  of nkCallKinds:
    if n[0].kind == nkSym and n[0].sym.magic == mSlice:
      result = canBorrow(n[1])
    else:
      # XXX: calls returning composite views are currently not treated as
      #      borrowable paths
      result = false
  of nkDotExpr, nkBracketExpr, nkCheckedFieldExpr:
    result = canBorrow(n[0])
  of nkHiddenStdConv, nkHiddenSubConv:
    # XXX: this is implemented multiple times in different places...
    if skipTypes(n.typ, abstractPtrs-{tyTypeDesc}).kind in {tyTuple, tyObject, tyOpenArray} or
       compareTypes(n.typ, n[1].typ, dcEqIgnoreDistinct):
      result = canBorrow(n[1])
    else:
      result = false
  of nkStmtListExpr:
    result = canBorrow(n[^1])
  else:
    result = false

proc root(n: PNode): PNode =
  case n.kind
  of nkSym, nkDerefExpr:
    result = n
  of PathKinds0 - {nkDerefExpr}:
    result = n[0].root
  of PathKinds1:
    result = n[1].root
  of nkCallKinds:
    result = n[1].root
  else:
    doAssert false

proc overlaps(a, b: PNode): bool =
  # TODO: use proper path aliasing analysis
  aliases(a, b) != no

proc report(config: ConfigRef, borrow, use: PNode, problem: Instr) =
  # TODO: report a better error for kills (i.e., the borrower outliving the borrowee)
  let rep = SemReport(kind: rsemIllegalBorrow, ast: borrow,
                      problem: problem.n.info, usage: use.info,
                      isProblemMutation: problem.kind == mut)
  config.localReport(borrow.info, rep)

proc isGlobal(p: PNode): bool =
  let r = root(p)
  if r.kind == nkSym and sfGlobal in r.sym.flags:
    result = true
  elif r.kind == nkDerefExpr:
    # treat pointer and ref indirections like globals
    result = true

proc verifyLocalBorrow(config: ConfigRef, c: ControlFlowGraph, start: int) =
  let path = c[start].n
  let target = c[start].borrower
  let isGlobal = isGlobal(path)
  let isMutable = target.sym.kind == skVar

  var exit = false
  var problem = -1
  for (i, instr) in traverse(c, start + 1, exit, problem):
    case instr.kind
    of def, kill:
      if instr.n.sym.id == target.sym.id:
        # if instr.n == target, then its the initial assignment
        # XXX: this is dangerous, because it relies on symbol nodes not being
        #      re-used
        if instr.n != target:
          # the borrower changes its borrows -> stop
          exit = true
      elif overlaps(path, instr.n):
        problem = i # mutation/kill of the borrowee
    of use:
      if overlaps(path, instr.n):
        if isMutable:
          problem = i # use of the borrowee
      elif problem != -1 and c[problem].kind != use and overlaps(target, instr.n):
        # problematic use of the borrower
        report(config, path, instr.n, c[problem])
        break
    of mut:
      if overlaps(path, instr.n):
        problem = i # mutation of the borrowee
      elif problem != -1 and overlaps(target, instr.n):
        # mutation of the borrower
        report(config, path, instr.n, c[problem])
        break
    of borrow:
      if overlaps(path, instr.n):
        if instr.borrower.kind == nkSym:
          if isMutable or instr.borrower.sym.kind == skVar:
            problem = i
        else:
          # a mutable borrow for a var parameter
          problem = i
    of call:
      if isGlobal and tfNoSideEffect notin instr.n[0].typ.skipTypes(abstractInst).flags:
        problem = i
    else:
      doAssert false

  if target.sym.kind == skResult and exit:
    # the borrow escapes; it must be a borrow from the first parameter
    if root(path).kind != nkSym or root(path).sym.kind != skParam:
      config.localReport(path.info,
        SemReport(kind: rsemResultMustBorrowFirst))

proc verifyParamBorrow(config: ConfigRef, c: ControlFlowGraph, start: int) =
  let path = c[start].n
  let target = c[start].borrower

  if isGlobal(path) and tfNoSideEffect notin target[0].typ.skipTypes(abstractInst).flags:
    config.localReport(path.info, SemReport(kind: rsemIllegalParamterBorrow))
    return

  var exit = false
  var problem = -1
  for (i, instr) in traverse(c, start + 1, exit, problem):
    case instr.kind
    of def, kill, mut:
      if overlaps(path, instr.n):
        problem = i # mutation/kill of the borrowee
    of use:
      if overlaps(path, instr.n):
        problem = i # use of the borrowee
    of borrow:
      if overlaps(path, instr.n):
        # TODO: must be a proper error
        echo "error: cannot reborrow at ", config.toFileLineCol(instr.n.info)
        break
    of call:
      if instr.n == target:
        # the call consumes the view
        break
    else:
      doAssert false

proc check*(config: ConfigRef, c: ControlFlowGraph) =
  for pos, it in c.pairs:
    if it.kind == borrow:
      case it.borrower.kind
      of nkSym:
        # borrow to local
        verifyLocalBorrow(config, c, pos)
      of nkCallKinds:
        # borrow to procedure parameter
        verifyParamBorrow(config, c, pos)
      else:
        config.internalError(it.n.info, $it.borrower.kind)
