#
#
#           The Nim Compiler
#        (c) Copyright 2012 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Simple alias analysis for the HLO and the code generators.


import
  std/[
    intsets
  ],
  compiler/ast/[
    ast,
    astalgo,
    types,
    trees,
    renderer
  ],
  compiler/sem/typeallowed

type
  TAnalysisResult* = enum
    arNo, arMaybe, arYes

proc isPartOfAux(a, b: PType, marker: var IntSet): TAnalysisResult

proc isPartOfAux(n: PNode, b: PType, marker: var IntSet): TAnalysisResult =
  result = arNo
  case n.kind
  of nkRecList:
    for i in 0..<n.len:
      result = isPartOfAux(n[i], b, marker)
      if result == arYes: return
  of nkRecCase:
    assert(n[0].kind == nkSym)
    result = isPartOfAux(n[0], b, marker)
    if result == arYes: return
    for i in 1..<n.len:
      case n[i].kind
      of nkOfBranch, nkElse:
        result = isPartOfAux(lastSon(n[i]), b, marker)
        if result == arYes: return
      else: discard "isPartOfAux(record case branch)"
  of nkSym:
    result = isPartOfAux(n.sym.typ, b, marker)
  else: discard

proc isPartOfAux(a, b: PType, marker: var IntSet): TAnalysisResult =
  result = arNo
  if a == nil or b == nil: return
  if containsOrIncl(marker, a.id): return
  if compareTypes(a, b, dcEqIgnoreDistinct): return arYes
  case a.kind
  of tyObject:
    if a[0] != nil:
      result = isPartOfAux(a[0].skipTypes(skipPtrs), b, marker)
    if result == arNo: result = isPartOfAux(a.n, b, marker)
  of tyGenericInst, tyDistinct, tyAlias, tySink:
    result = isPartOfAux(lastSon(a), b, marker)
  of tyArray, tySet, tyTuple:
    for i in 0..<a.len:
      result = isPartOfAux(a[i], b, marker)
      if result == arYes: return
  else: discard

proc isPartOf(a, b: PType): TAnalysisResult =
  ## checks iff 'a' can be part of 'b'. Iterates over VALUE types!
  var marker = initIntSet()
  # watch out: parameters reversed because I'm too lazy to change the code...
  result = isPartOfAux(b, a, marker)

type
  OpKind = enum
    okUnknown
    okUnique
    okSym
    okDeref
    okArr
    okRecord
    okViewCall
    okCall

  Op = object
    case kind: OpKind
    of okSym: sym {.cursor.}: PSym
    of okArr: index {.cursor.}: PNode
    of okRecord: position: int
    of okDeref: typ {.cursor.}: PType
    else: nil

proc gen(ops: var seq[Op], a: PNode) =
  case a.kind
  of nkLiterals, nkNilLit:
    ops.add Op(kind: okUnique)
  of nkDotExpr:
    gen(ops, a[0])
    ops.add Op(kind: okRecord, position: a[1].sym.position)
  of nkStmtListExpr:
    gen(ops, a.lastSon)
  of nkCallKinds:
    if a[0].kind == nkSym and a[0].sym.magic == mNoAlias:
      ops.add Op(kind: okUnique)
    elif classifyViewType(a.typ) != noView:
      gen(ops, a[1])
      ops.add Op(kind: okViewCall)
    else:
      ops.add Op(kind: okCall)
  of nkHiddenSubConv, nkConv, nkHiddenStdConv:
    gen(ops, a[1])
  of nkObjUpConv, nkObjDownConv, nkCheckedFieldExpr:
    gen(ops, a[0])
  of nkDerefExpr, nkHiddenDeref:
    gen(ops, a[0])
    ops.add Op(kind: okDeref, typ: a.typ)
  of nkBracketExpr:
    gen(ops, a[0])
    case a[0].typ.skipTypes(abstractVar).kind
    of tyTuple:
      ops.add Op(kind: okRecord, position: a[1].intVal.int)
    else:
      ops.add Op(kind: okArr, index: a[1])
  of nkSym:
    ops.add Op(kind: okSym, sym: a.sym)
  of nkCast, nkCurly, nkBracket, nkObjConstr, nkTupleConstr, nkAddr:
    # a cast produces a new value, so we treat it as a call
    ops.add Op(kind: okCall)
  of nkIfExpr, nkCaseStmt, nkBlockExpr, nkTryStmt, nkHiddenTryStmt:
    ops.add Op(kind: okCall)
  else:
    ops.add Op(kind: okUnknown)

proc compare(a, b: Op, prev: TAnalysisResult): TAnalysisResult =
  result = prev
  if a.kind == b.kind:
    case a.kind
    of okSym:
      if a.sym.id == b.sym.id:
        result = arYes
    of okUnknown:
      result = arMaybe
    of okArr:
      if result == arYes and isDeepConstExpr(a.index) and isDeepConstExpr(b.index):
        if sameValue(a.index, b.index): result = arYes
        else: result = arNo
      # else: keep as is
    of okRecord:
      if a.position != b.position:
        result = arNo
    of okDeref:
      # no need to perform the expensive type check if the expressions match already
      if result != arYes:
        result =
          if sameType(a.typ, b.typ): arMaybe
          else: arNo
    of okViewCall:
      if result == arYes:
        result = arMaybe
    of okCall:
      result = arNo
    else:
      doAssert false, $a.kind
  else:
    proc check(a, b: Op): TAnalysisResult =
      case a.kind
      of okCall:
        result = arNo
      of okViewCall:
        result = arMaybe
      of okArr, okRecord:
        result = arNo
      of okDeref:
        result = arMaybe#isPartOf(a.typ, b.typ)
      of okUnknown:
        result = arMaybe
      of okSym:
        # one side is a symbol, the other one is not
        result = arNo
      else:
        echo "whut: ", a.kind

    result = check(a, b)

    if result != arYes:
      result = check(b, a)

proc analyse(op1, op2: openArray[Op]): TAnalysisResult =
  if op1[0].kind == okUnique or op2[0].kind == okUnique:
    # at least one of the expression starts from a unique value
    return arNo

  var i = 0
  while i < op1.len and i < op2.len:
    result = compare(op1[i], op2[i], result)

    inc i

proc isPartOf*(a, b: PNode): TAnalysisResult =
  ## checks if location `a` can be part of location `b`. We treat seqs and
  ## strings as pointers because the code gen often just passes them as such.
  ##
  ## Note: `a` can only be part of `b`, if `a`'s type can be part of `b`'s
  ## type. Since however type analysis is more expensive, we perform it only
  ## if necessary.
  ##
  ## cases:
  ##
  ## YES-cases:
  ##  x    <| x   # for general trees
  ##  x[]  <| x
  ##  x[i] <| x
  ##  x.f  <| x
  ##
  ## NO-cases:
  ## x           !<| y    # depending on type and symbol kind
  ## x[constA]   !<| x[constB]
  ## x.f         !<| x.g
  ## x.f         !<| y.f  iff x !<= y
  ##
  ## MAYBE-cases:
  ##
  ##  x[] ?<| y[]   iff compatible type
  ##
  ##
  ##  x[]  ?<| y  depending on type
  ##
  var op1, op2: seq[Op]
  gen(op1, a)
  gen(op2, b)

  result = analyse(op1, op2)

  if result != arNo:
    echo op1
    echo op2
    echo "is '", renderTree(a), "' part of '", renderTree(b), "': ", result

  # if a.kind == b.kind:
  #   case a.kind
  #   of nkSym:
  #     const varKinds = {skResult, skVar, skTemp, skProc, skFunc}
  #     # same symbol: aliasing:
  #     if a.sym.id == b.sym.id: result = arYes
  #     elif a.sym.kind in varKinds or b.sym.kind in varKinds:
  #       # actually, a param could alias a var but we know that cannot happen
  #       # here. XXX make this more generic
  #       result = arNo
  #     else:
  #       # use expensive type check:
  #       if isPartOf(a.sym.typ, b.sym.typ) != arNo:
  #         result = arMaybe
  #   of nkBracketExpr:
  #     result = isPartOf(a[0], b[0])
  #     if a.len >= 2 and b.len >= 2:
  #       # array accesses:
  #       if result == arYes and isDeepConstExpr(a[1]) and isDeepConstExpr(b[1]):
  #         # we know it's the same array and we have 2 constant indexes;
  #         # if they are
  #         var x = if a[1].kind == nkHiddenStdConv: a[1][1] else: a[1]
  #         var y = if b[1].kind == nkHiddenStdConv: b[1][1] else: b[1]
  #
  #         if sameValue(x, y): result = arYes
  #         else: result = arNo
  #       # else: maybe and no are accurate
  #     else:
  #       # pointer derefs:
  #       if result != arYes:
  #         if isPartOf(a.typ, b.typ) != arNo: result = arMaybe
  #
  #   of nkDotExpr:
  #     result = isPartOf(a[0], b[0])
  #     if result != arNo:
  #       # if the fields are different, it's not the same location
  #       if a[1].sym.id != b[1].sym.id:
  #         result = arNo
  #
  #   of nkHiddenDeref, nkDerefExpr:
  #     result = isPartOf(a[0], b[0])
  #     # weaken because of indirection:
  #     if result != arYes:
  #       if isPartOf(a.typ, b.typ) != arNo: result = arMaybe
  #
  #   of nkHiddenStdConv, nkHiddenSubConv, nkConv:
  #     result = isPartOf(a[1], b[1])
  #   of nkObjUpConv, nkObjDownConv, nkCheckedFieldExpr:
  #     result = isPartOf(a[0], b[0])
  #   else: discard
  #   # Calls return a new location, so a default of ``arNo`` is fine.
  # else:
  #   # go down recursively; this is quite demanding:
  #   const
  #     Ix0Kinds = {nkDotExpr, nkBracketExpr, nkObjUpConv, nkObjDownConv,
  #                 nkCheckedFieldExpr, nkHiddenAddr}
  #     Ix1Kinds = {nkHiddenStdConv, nkHiddenSubConv, nkConv}
  #     DerefKinds = {nkHiddenDeref, nkDerefExpr}
  #   case b.kind
  #   of Ix0Kinds:
  #     # a* !<| b.f  iff  a* !<| b
  #     result = isPartOf(a, b[0])
  #
  #   of DerefKinds:
  #     # a* !<| b[] iff
  #     if isPartOf(a.typ, b.typ) != arNo:
  #       result = isPartOf(a, b[0])
  #       if result == arNo: result = arMaybe
  #
  #   of Ix1Kinds:
  #     # a* !<| T(b)  iff a* !<| b
  #     result = isPartOf(a, b[1])
  #
  #   of nkSym:
  #     # b is an atom, so we have to check a:
  #     case a.kind
  #     of Ix0Kinds:
  #       # a.f !<| b*  iff  a.f !<| b*
  #       result = isPartOf(a[0], b)
  #     of Ix1Kinds:
  #       result = isPartOf(a[1], b)
  #
  #     of DerefKinds:
  #       if isPartOf(a.typ, b.typ) != arNo:
  #         result = isPartOf(a[0], b)
  #         if result == arNo: result = arMaybe
  #     else: discard
  #   of nkObjConstr:
  #     result = arNo
  #     for i in 1..<b.len:
  #       let res = isPartOf(a, b[i][1])
  #       if res != arNo:
  #         result = res
  #         if res == arYes: break
  #   of nkCallKinds:
  #     result = arNo
  #     for i in 1..<b.len:
  #       let res = isPartOf(a, b[i])
  #       if res != arNo:
  #         result = res
  #         if res == arYes: break
  #   of nkBracket:
  #     if b.len > 0:
  #       result = isPartOf(a, b[0])
  #   of nkLiterals:
  #     # literals never alias with anything else (even themselves)
  #     result = arNo
  #   else: discard
