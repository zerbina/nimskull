#
#
#           The Nim Compiler
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## this module folds constants; used by semantic checking phase
## and evaluation phase

import
  std/[
    strutils,
    strtabs,
    math,
  ],
  compiler/ast/[
    renderer,
    types,
    nimsets,
    ast,
    trees,
    lineinfos,
    errorhandling,
  ],
  compiler/modules/[
    magicsys,
    modulegraphs,
  ],
  compiler/front/[
    options,
  ],
  compiler/utils/[
    platform,
    idioms,
  ]

# xxx: legacy reports cruft
from compiler/front/msgs import internalError

from system/memory import nimCStrLen

type
  Folded = object
    ## Helper type for tracking/passing contextual state during constant
    ## folding.
    node: PNode ## the AST of the processed expression/statement
    i: int      ## where to insert the next node
    allConst, hasError: bool

const
  ExpressionNodes = {
    nkSym, nkEmpty, nkNimNodeLit, nkNilLit,
    nkRange, nkBracket, nkCurly, nkObjConstr, nkTupleConstr,
    nkDotExpr, nkCheckedFieldExpr, nkBracketExpr, nkHiddenDeref, nkDerefExpr, nkAddr, nkHiddenAddr,
    nkCast, nkConv, nkHiddenStdConv, nkHiddenSubConv,
    nkTypeOfExpr,
    nkIfExpr, nkStmtListExpr, nkError} + nkCallKinds + nkLiterals
    ## nodes considered expressions during constant folding

  Evaluateable = ExpressionNodes - {nkHiddenAddr}
    ## nodes that the simple, AST-based evaluator can process

func fromAst(n: PNode, num: int): Folded =
  result = Folded(node: n, i: num, allConst: false)

proc cow(n: var PNode, num: int) =
  if nfCopied notin n.flags:
    let orig = n
    n = shallowCopy(orig)
    n.flags.incl nfCopied
    # only copy the nodes up-to `num`, the rest
    # is copied manually
    for i in 0..<num:
      n[i] = orig[i]

proc add(x: var Folded, y: sink Folded) =
  ## Appends `y` to `x` and propagates the const-ness.
  if x.node[x.i] != y.node:
    cow(x.node, x.i)
    x.node[x.i] = y.node

  inc x.i
  # propagate const-ness and error-ness
  x.allConst = x.allConst and y.allConst
  x.hasError = x.hasError or y.hasError

proc addConst(f: var Folded, n: PNode) =
  ## Appends `n` to `f`, where `n` is known to be constant.
  if f.node[f.i] != n:
    cow(f.node, f.i)
    f.node[f.i] = n

  inc f.i
  let err = n.isError
  f.allConst = f.allConst and (not err)
  f.hasError = f.hasError or err

proc errorType*(g: ModuleGraph): PType =
  ## creates a type representing an error state
  result = newType(tyError, nextTypeId(g.idgen), g.owners[^1])
  result.flags.incl tfCheckedForDestructor

proc getIntLitTypeG(g: ModuleGraph; literal: PNode; idgen: IdGenerator): PType =
  # we cache some common integer literal types for performance:
  let ti = getSysType(g, literal.info, tyInt)
  result = copyType(ti, nextTypeId(idgen), ti.owner)
  result.n = literal

proc newIntNodeT*(intVal: Int128, n: PNode; idgen: IdGenerator; g: ModuleGraph): PNode =
  result = newIntTypeNode(intVal, n.typ)
  # See bug #6989. 'pred' et al only produce an int literal type if the
  # original type was 'int', not a distinct int etc.
  if n.typ.kind == tyInt:
    # access cache for the int lit type
    result.typ = getIntLitTypeG(g, result, idgen)
  result.info = n.info

proc newFloatNodeT*(floatVal: BiggestFloat, n: PNode; g: ModuleGraph): PNode =
  if n.typ.skipTypes(abstractInst).kind == tyFloat32:
    result = newFloatNode(nkFloat32Lit, floatVal)
  else:
    result = newFloatNode(nkFloatLit, floatVal)
  result.typ = n.typ
  result.info = n.info

proc newStrNodeT*(strVal: string, n: PNode; g: ModuleGraph): PNode =
  result = newStrNode(nkStrLit, strVal)
  result.typ = n.typ
  result.info = n.info

proc checkInRange(conf: ConfigRef; n: PNode, res: Int128): bool =
  res in firstOrd(conf, n.typ)..lastOrd(conf, n.typ)

proc foldAdd(a, b: Int128, n: PNode; idgen: IdGenerator; g: ModuleGraph): PNode =
  let res = a + b
  if checkInRange(g.config, n, res):
    result = newIntNodeT(res, n, idgen, g)

proc foldSub(a, b: Int128, n: PNode; idgen: IdGenerator; g: ModuleGraph): PNode =
  let res = a - b
  if checkInRange(g.config, n, res):
    result = newIntNodeT(res, n, idgen, g)

proc foldUnarySub(a: Int128, n: PNode; idgen: IdGenerator, g: ModuleGraph): PNode =
  if a != firstOrd(g.config, n.typ):
    result = newIntNodeT(-a, n, idgen, g)

proc foldAbs(a: Int128, n: PNode; idgen: IdGenerator; g: ModuleGraph): PNode =
  if a != firstOrd(g.config, n.typ):
    result = newIntNodeT(abs(a), n, idgen, g)

proc foldMul(a, b: Int128, n: PNode; idgen: IdGenerator; g: ModuleGraph): PNode =
  let res = a * b
  if checkInRange(g.config, n, res):
    return newIntNodeT(res, n, idgen, g)

proc ordinalValToString(a: PNode; g: ModuleGraph): string =
  # because $ has the param ordinal[T], `a` is not necessarily an enum, but an
  # ordinal
  case a.kind
  of nkIntLiterals:
    let
      x = getInt(a)
      t = skipTypes(a.typ, abstractRange)
    case t.kind
    of tyChar:
      result = $chr(toInt64(x) and 0xff)
    of tyEnum:
      let n = t.n
      for i in 0..<n.len:
        case n[i].kind
        of nkSym:
          let field = n[i].sym
          if field.position == x:
            if field.ast == nil:
              return field.name.s
            else:
              return field.ast.strVal
        of nkError:
          g.config.internalError(n[i].info, "ordinalValToString")
        else:
          unreachable("ordinalValToString")
      if n.len > 0:
        unreachable("range checking `semConv` eliminates this case")
    else:
      result = $x
  of nkError:
    g.config.internalError(a.info, "ordinalValToString")
  else:
    unreachable("non-ordinals never make it here")

proc isFloatRange(t: PType): bool {.inline.} =
  result = t.kind == tyRange and t[0].kind in {tyFloat..tyFloat128}

proc isIntRange(t: PType): bool {.inline.} =
  result = t.kind == tyRange and t[0].kind in {
      tyInt..tyInt64, tyUInt8..tyUInt32}

proc pickIntRange(a, b: PType): PType =
  if isIntRange(a): result = a
  elif isIntRange(b): result = b
  else: result = a

proc isIntRangeOrLit(t: PType): bool =
  result = isIntRange(t) or isIntLit(t)

proc evalOp*(m: TMagic, n, a, b, c: PNode; idgen: IdGenerator; g: ModuleGraph): PNode =
  # b and c may be nil
  result = nil
  case m
  of mOrd: result = newIntNodeT(getOrdValue(a), n, idgen, g)
  of mChr: result = newIntNodeT(getInt(a), n, idgen, g)
  of mUnaryMinusI, mUnaryMinusI64: result = foldUnarySub(getInt(a), n, idgen, g)
  of mUnaryMinusF64: result = newFloatNodeT(-getFloat(a), n, g)
  of mNot: result = newIntNodeT(One - getInt(a), n, idgen, g)
  of mCard: result = newIntNodeT(toInt128(nimsets.cardSet(g.config, a)), n, idgen, g)
  of mBitnotI:
    if n.typ.isUnsigned:
      result = newIntNodeT(bitnot(getInt(a)).maskBytes(int(n.typ.size)), n, idgen, g)
    else:
      result = newIntNodeT(bitnot(getInt(a)), n, idgen, g)
  of mLengthArray: result = newIntNodeT(lengthOrd(g.config, a.typ), n, idgen, g)
  of mLengthSeq, mLengthOpenArray, mLengthStr:
    if a.kind == nkNilLit:
      result = newIntNodeT(Zero, n, idgen, g)
    elif a.kind in {nkStrLit..nkTripleStrLit}:
      if a.typ.kind == tyString:
        result = newIntNodeT(toInt128(a.strVal.len), n, idgen, g)
      elif a.typ.kind == tyCstring:
        result = newIntNodeT(toInt128(nimCStrLen(a.strVal.cstring)), n, idgen, g)
    else:
      result = newIntNodeT(toInt128(a.len), n, idgen, g)
  of mUnaryPlusI, mUnaryPlusF64: result = a # throw `+` away
  # XXX: Hides overflow/underflow
  of mAbsI: result = foldAbs(getInt(a), n, idgen, g)
  of mSucc: result = foldAdd(getOrdValue(a), getInt(b), n, idgen, g)
  of mPred: result = foldSub(getOrdValue(a), getInt(b), n, idgen, g)
  of mAddI: result = foldAdd(getInt(a), getInt(b), n, idgen, g)
  of mSubI: result = foldSub(getInt(a), getInt(b), n, idgen, g)
  of mMulI: result = foldMul(getInt(a), getInt(b), n, idgen, g)
  of mMinI:
    let argA = getInt(a)
    let argB = getInt(b)
    result = newIntNodeT(if argA < argB: argA else: argB, n, idgen, g)
  of mMaxI:
    let argA = getInt(a)
    let argB = getInt(b)
    result = newIntNodeT(if argA > argB: argA else: argB, n, idgen, g)
  of mShlI:
    case skipTypes(n.typ, abstractRange).kind
    of tyInt8: result = newIntNodeT(toInt128(toInt8(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
    of tyInt16: result = newIntNodeT(toInt128(toInt16(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
    of tyInt32: result = newIntNodeT(toInt128(toInt32(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
    of tyInt64: result = newIntNodeT(toInt128(toInt64(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
    of tyInt:
      if g.config.target.intSize == 4:
        result = newIntNodeT(toInt128(toInt32(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
      else:
        result = newIntNodeT(toInt128(toInt64(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
    of tyUInt8: result = newIntNodeT(toInt128(toUInt8(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
    of tyUInt16: result = newIntNodeT(toInt128(toUInt16(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
    of tyUInt32: result = newIntNodeT(toInt128(toUInt32(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
    of tyUInt64: result = newIntNodeT(toInt128(toUInt64(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
    of tyUInt:
      if g.config.target.intSize == 4:
        result = newIntNodeT(toInt128(toUInt32(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
      else:
        result = newIntNodeT(toInt128(toUInt64(getInt(a)) shl toInt64(getInt(b))), n, idgen, g)
    else:
      unreachable("constant folding for shl")
  of mShrI:
    var a = cast[uint64](getInt(a))
    let b = cast[uint64](getInt(b))
    # To support the ``-d:nimOldShiftRight`` flag, we need to mask the
    # signed integers to cut off the extended sign bit in the internal
    # representation.
    if 0'u64 < b: # do not cut off the sign extension, when there is
              # no bit shifting happening.
      case skipTypes(n.typ, abstractRange).kind
      of tyInt8: a = a and 0xff'u64
      of tyInt16: a = a and 0xffff'u64
      of tyInt32: a = a and 0xffffffff'u64
      of tyInt:
        if g.config.target.intSize == 4:
          a = a and 0xffffffff'u64
      else:
        # unsigned and 64 bit integers don't need masking
        discard
    let c = cast[BiggestInt](a shr b)
    result = newIntNodeT(toInt128(c), n, idgen, g)
  of mAshrI:
    case skipTypes(n.typ, abstractRange).kind
    of tyInt8: result =  newIntNodeT(toInt128(ashr(toInt8(getInt(a)), toInt8(getInt(b)))), n, idgen, g)
    of tyInt16: result = newIntNodeT(toInt128(ashr(toInt16(getInt(a)), toInt16(getInt(b)))), n, idgen, g)
    of tyInt32: result = newIntNodeT(toInt128(ashr(toInt32(getInt(a)), toInt32(getInt(b)))), n, idgen, g)
    of tyInt64, tyInt:
      result = newIntNodeT(toInt128(ashr(toInt64(getInt(a)), toInt64(getInt(b)))), n, idgen, g)
    else:
      unreachable("constant folding for ashr")
  of mDivI:
    let argA = getInt(a)
    let argB = getInt(b)
    if argB != Zero and (argA != firstOrd(g.config, n.typ) or argB != NegOne):
      result = newIntNodeT(argA div argB, n, idgen, g)
  of mModI:
    let argA = getInt(a)
    let argB = getInt(b)
    if argB != Zero and (argA != firstOrd(g.config, n.typ) or argB != NegOne):
      result = newIntNodeT(argA mod argB, n, idgen, g)
  of mAddF64: result = newFloatNodeT(getFloat(a) + getFloat(b), n, g)
  of mSubF64: result = newFloatNodeT(getFloat(a) - getFloat(b), n, g)
  of mMulF64: result = newFloatNodeT(getFloat(a) * getFloat(b), n, g)
  of mDivF64:
    result = newFloatNodeT(getFloat(a) / getFloat(b), n, g)
  of mIsNil: result = newIntNodeT(toInt128(ord(a.kind == nkNilLit)), n, idgen, g)
  of mLtI, mLtB, mLtEnum, mLtCh:
    result = newIntNodeT(toInt128(ord(getOrdValue(a) < getOrdValue(b))), n, idgen, g)
  of mLeI, mLeB, mLeEnum, mLeCh:
    result = newIntNodeT(toInt128(ord(getOrdValue(a) <= getOrdValue(b))), n, idgen, g)
  of mEqI, mEqB, mEqEnum, mEqCh:
    result = newIntNodeT(toInt128(ord(getOrdValue(a) == getOrdValue(b))), n, idgen, g)
  of mLtF64: result = newIntNodeT(toInt128(ord(getFloat(a) < getFloat(b))), n, idgen, g)
  of mLeF64: result = newIntNodeT(toInt128(ord(getFloat(a) <= getFloat(b))), n, idgen, g)
  of mEqF64: result = newIntNodeT(toInt128(ord(getFloat(a) == getFloat(b))), n, idgen, g)
  of mLtStr: result = newIntNodeT(toInt128(ord(getStr(a) < getStr(b))), n, idgen, g)
  of mLeStr: result = newIntNodeT(toInt128(ord(getStr(a) <= getStr(b))), n, idgen, g)
  of mEqStr: result = newIntNodeT(toInt128(ord(getStr(a) == getStr(b))), n, idgen, g)
  of mLtU:
    result = newIntNodeT(toInt128(ord(`<%`(toInt64(getOrdValue(a)), toInt64(getOrdValue(b))))), n, idgen, g)
  of mLeU:
    result = newIntNodeT(toInt128(ord(`<=%`(toInt64(getOrdValue(a)), toInt64(getOrdValue(b))))), n, idgen, g)
  of mBitandI, mAnd: result = newIntNodeT(bitand(a.getInt, b.getInt), n, idgen, g)
  of mBitorI, mOr: result = newIntNodeT(bitor(getInt(a), getInt(b)), n, idgen, g)
  of mBitxorI, mXor: result = newIntNodeT(bitxor(getInt(a), getInt(b)), n, idgen, g)
  of mAddU:
    let val = maskBytes(getInt(a) + getInt(b), int(n.typ.size))
    result = newIntNodeT(val, n, idgen, g)
  of mSubU:
    let val = maskBytes(getInt(a) - getInt(b), int(n.typ.size))
    result = newIntNodeT(val, n, idgen, g)
    # echo "subU: ", val, " n: ", n, " result: ", val
  of mMulU:
    let val = maskBytes(getInt(a) * getInt(b), int(n.typ.size))
    result = newIntNodeT(val, n, idgen, g)
  of mModU:
    let argA = maskBytes(getInt(a), int(a.typ.size))
    let argB = maskBytes(getInt(b), int(a.typ.size))
    if argB != Zero:
      result = newIntNodeT(argA mod argB, n, idgen, g)
  of mDivU:
    let argA = maskBytes(getInt(a), int(a.typ.size))
    let argB = maskBytes(getInt(b), int(a.typ.size))
    if argB != Zero:
      result = newIntNodeT(argA div argB, n, idgen, g)
  of mLeSet: result = newIntNodeT(toInt128(ord(containsSets(g.config, b, a))), n, idgen, g)
  of mEqSet: result = newIntNodeT(toInt128(ord(equalSets(g.config, a, b))), n, idgen, g)
  of mLtSet:
    result = newIntNodeT(toInt128(ord(
      containsSets(g.config, b, a) and not equalSets(g.config, a, b))), n, idgen, g)
  of mMulSet:
    result = nimsets.intersectSets(g.config, a, b)
    result.info = n.info
  of mPlusSet:
    result = nimsets.unionSets(g.config, a, b)
    result.info = n.info
  of mMinusSet:
    result = nimsets.diffSets(g.config, a, b)
    result.info = n.info
  of mConStrStr: result = newStrNodeT(getStrOrChar(a) & getStrOrChar(b), n, g)
  of mInSet: result = newIntNodeT(toInt128(ord(inSet(a, b))), n, idgen, g)
  of mRepr:
    # BUGFIX: we cannot eval mRepr here for reasons that I forgot.
    discard
  of mIntToStr, mInt64ToStr: result = newStrNodeT($(getOrdValue(a)), n, g)
  of mBoolToStr:
    if getOrdValue(a) == 0: result = newStrNodeT("false", n, g)
    else: result = newStrNodeT("true", n, g)
  of mFloatToStr: result = newStrNodeT($getFloat(a), n, g)
  of mCStrToStr, mCharToStr:
    result = newStrNodeT(getStrOrChar(a), n, g)
  of mStrToStr: result = newStrNodeT(getStrOrChar(a), n, g)
  of mEnumToStr: result = newStrNodeT(ordinalValToString(a, g), n, g)
  of mArrToSeq:
    result = modify(a)
    result.typ = n.typ
  of mEqProc:
    result = newIntNodeT(toInt128(ord(
        exprStructuralEquivalent(a, b, strictSymEquality=true))), n, idgen, g)
  else: discard

proc getConstIfExpr(n: PNode): PNode =
  ## Folds a fully constant 'if' expression into the first branch where
  ## the condition expression is 'true'.
  for it in n.items:
    case it.kind
    of nkElifExpr, nkElifBranch:
      if getOrdValue(it[0]) != 0:
        # a branch where the condition is statically 'true'
        result = it[1]
        break
      # ignore false
    of nkElseExpr, nkElse:
      # the condition of all other branches is known to evaluate to 'false',
      # meaning that the 'else' branch can be chosen
      result = it[0]
    else:
      unreachable(it.kind)

  assert result != nil

proc leValueConv*(a, b: PNode): bool =
  result = false
  case a.kind
  of nkCharLit..nkUInt64Lit:
    case b.kind
    of nkCharLit..nkUInt64Lit: result = a.getInt <= b.getInt
    of nkFloatLit..nkFloat128Lit: result = a.intVal <= round(b.floatVal).int
    else: result = false #internalError(a.info, "leValueConv")
  of nkFloatLit..nkFloat128Lit:
    case b.kind
    of nkFloatLit..nkFloat128Lit: result = a.floatVal <= b.floatVal
    of nkCharLit..nkUInt64Lit: result = a.floatVal <= toFloat64(b.getInt)
    else: result = false # internalError(a.info, "leValueConv")
  else: result = false # internalError(a.info, "leValueConv")

proc getAppType(n: PNode; g: ModuleGraph): PNode =
  if g.config.globalOptions.contains(optGenDynLib):
    result = newStrNodeT("lib", n, g)
  elif g.config.globalOptions.contains(optGenStaticLib):
    result = newStrNodeT("staticlib", n, g)
  elif g.config.globalOptions.contains(optGenGuiApp):
    result = newStrNodeT("gui", n, g)
  else:
    result = newStrNodeT("console", n, g)

proc foldConv(n, a: PNode; idgen: IdGenerator; g: ModuleGraph; check = false): PNode =
  let dstTyp = skipTypes(n.typ, abstractRange - {tyTypeDesc})
  let srcTyp = skipTypes(a.typ, abstractRange - {tyTypeDesc})

  template rangeCheck(n: PNode, value: Int128, g: ModuleGraph): bool =
    value >= firstOrd(g.config, n.typ) and value <= lastOrd(g.config, n.typ)

  template rangeError(n, a: PNode, g: ModuleGraph): PNode =
    newError(g.config, n,
             PAstDiag(kind: adSemFoldRangeCheckForLiteralConversionFailed,
                      inputLit: a))

  const
    IntegerLike = {tyInt..tyInt64, tyUInt..tyUInt64, tyChar}
    FloatLike   = {tyFloat..tyFloat64}

  case dstTyp.kind
  of tyBool:
    case srcTyp.kind
    of FloatLike:
      result = newIntNodeT(toInt128(getFloat(a) != 0.0), n, idgen, g)
    of IntegerLike:
      result = newIntNodeT(toInt128(a.getOrdValue != 0), n, idgen, g)
    of tyBool, tyEnum: # xxx shouldn't we disallow `tyEnum`?
      result = modify(a)
      result.typ = n.typ
    else: unreachable(srcTyp.kind)
  of IntegerLike:
    let val =
      case srcTyp.kind
      of IntegerLike, tyEnum, tyBool: getOrdValue(a)
      of FloatLike:                   toInt128(getFloat(a))
      else:                           unreachable(srcTyp.kind)

    if check and not rangeCheck(n, val, g):
      result = rangeError(n, a, g)
    else:
      result = newIntNodeT(val, n, idgen, g)
  of FloatLike:
    case srcTyp.kind
    of IntegerLike, tyEnum, tyBool:
      result = newFloatNodeT(toFloat64(getOrdValue(a)), n, g)
    of FloatLike:
      result = newFloatNodeT(a.floatVal, n, g)
    else:
      unreachable(srcTyp.kind)
  of tyOpenArray, tyVarargs, tyProc, tyPointer:
    discard
  else:
    # FIXME: conversion-to-enum is missing checks
    result = modify(a)
    result.typ = n.typ

proc fold(e: PNode, g: ModuleGraph): PNode

proc foldArrayAccess(n: PNode, g: ModuleGraph): PNode =
  if n[0].typ.kind == tyTypeDesc:
    # this is a type construction
    # XXX: fold into an ``nkType`` here?
    return n

  # it's possible that the array expression is something dependent
  # on a constant that wasn't inlined. For the access, we do expand
  # it
  let
    x = fold(n[0], g)
    y = n[1]

  template outOfBounds(n, x, y: PNode, c: ConfigRef): PNode =
    c.newError(n, PAstDiag(kind: adSemIndexOutOfBoundsStatic,
                           staticCollection: x,
                           staticIndex: y))

  var idx = toInt64(getOrdValue(y))
  case x.kind
  of nkTupleConstr:
    if 0 <= idx and idx < x.len:
      result = x.sons[idx]
      if result.kind == nkExprColonExpr: result = result[1]
    else:
      result = outOfBounds(n, x, y, g.config)

  of nkBracket:
    idx -= toInt64(firstOrd(g.config, x.typ))
    if 0 <= idx and idx < x.len:
      result = x[int(idx)]
    else:
      result = outOfBounds(n, x, y, g.config)

  of nkStrLit..nkTripleStrLit:
    if 0 <= idx and idx < x.strVal.len:
      result = newNodeIT(nkCharLit, x.info, n.typ)
      result.intVal = ord(x.strVal[int(idx)])
    else:
      result = outOfBounds(n, x, y, g.config)

  else:
    # not a constant expression
    result = nil

proc foldFieldAccess(n: PNode, g: ModuleGraph): PNode =
  # a real field access; proc calls have already been transformed
  let x = fold(n[0], g)
  if x.kind notin {nkObjConstr, nkTupleConstr}:
    return

  let field = n[1].sym
  for i in ord(x.kind == nkObjConstr)..<x.len:
    var it = x[i]
    if it.kind != nkExprColonExpr:
      # lookup per index:
      result = x[field.position]
      if result.kind == nkExprColonExpr: result = result[1]
      return
    if it[0].sym.name.id == field.name.id:
      result = x[i][1]
      return

  g.config.newError(n, PAstDiag(kind: adSemStaticFieldNotFound,
                                unknownSym: field))


proc foldConStrStr(m: PSym, n: PNode, idgen: IdGenerator; g: ModuleGraph): PNode =
  result = newNodeIT(nkStrLit, n.info, n.typ)
  result.strVal = ""
  for i in 1..<n.len:
    result.strVal.add(getStrOrChar(n[i]))

proc newSymNodeTypeDesc*(s: PSym; idgen: IdGenerator; info: TLineInfo): PNode =
  result = newSymNode(s, info)
  if s.typ.kind != tyTypeDesc:
    result.typ = newType(tyTypeDesc, idgen.nextTypeId, s.owner)
    result.typ.addSonSkipIntLit(s.typ, idgen)
  else:
    result.typ = s.typ

proc fold(e: PNode, g: ModuleGraph): PNode =
  ## Given the fully constant expression `e`, returns the folded
  ## expression with complex constants inlined.
  case e.kind
  of nkDotExpr:
    foldFieldAccess(e, g)
  of nkBracketExpr:
    foldArrayAccess(e, g)
  of nkCallKinds:
    if e[0].sym.magic == mArrToSeq:
      fold(e[1], g)
    else:
      e
  of nkSym:
    if e.sym.kind == skConst: e.sym.ast
    else:                     e
  else:
    e # nothing to expand

proc fold2(e: PNode, i: int, g: ModuleGraph): PNode =
  if i < e.len: fold(e[i], g)
  else:         nil

proc getArrayConstr(n: PNode; g: ModuleGraph): PNode =
  if n.kind == nkBracket:
    result = n
  elif nfAllConst in n.flags:
    result = fold(n, g)
  else:
    result = n

proc getConstExpr(m: PSym, n: PNode; allConst: bool, idgen: IdGenerator; g: ModuleGraph): PNode =
  ## Evaluates the constant expression or returns nil if it is no constant
  ## expression. `allConst` indicates whether all operands are constant.
  result = nil
  case n.kind
  of nkSym:
    var s = n.sym
    case s.kind
    of skEnumField:
      # XXX: transforming enum field symbols during constant folding is too
      #      early... It should happen later
      result = newIntNodeT(toInt128(s.position), n, idgen, g)
    of skConst:
      case s.magic
      of mIsMainModule: result = newIntNodeT(toInt128(ord(sfMainModule in m.flags)), n, idgen, g)
      of mCompileDate: result = newStrNodeT(getDateStr(), n, g)
      of mCompileTime: result = newStrNodeT(getClockStr(), n, g)
      of mCpuEndian: result = newIntNodeT(toInt128(ord(CPU[g.config.target.targetCPU].endian)), n, idgen, g)
      of mHostOS: result = newStrNodeT(toLowerAscii(platform.OS[g.config.target.targetOS].name), n, g)
      of mHostCPU: result = newStrNodeT(platform.CPU[g.config.target.targetCPU].name.toLowerAscii, n, g)
      of mBuildOS: result = newStrNodeT(toLowerAscii(platform.OS[g.config.target.hostOS].name), n, g)
      of mBuildCPU: result = newStrNodeT(platform.CPU[g.config.target.hostCPU].name.toLowerAscii, n, g)
      of mAppType: result = getAppType(n, g)
      of mStrDefine, mIntDefine, mBoolDefine:
        result =
          if isDefined(g.config, s.name.s):
            let define = g.config.symbols[s.name.s]
            case s.magic
            of mStrDefine:
              newStrNodeT(define, n, g)
            of mIntDefine:
              try:
                newIntNodeT(toInt128(define.parseInt), n, idgen, g)
              except ValueError:
                g.config.newError(n, PAstDiag(kind: adSemInvalidIntDefine,
                                              invalidDef: define))
            of mBoolDefine:
              try:
                newIntNodeT(toInt128(define.parseBool.int), n, idgen, g)
              except ValueError:
                g.config.newError(n, PAstDiag(kind: adSemInvalidBoolDefine,
                                              invalidDef: define))
            else:
              unreachable("guarded by outer case branch")
          else:
            s.ast
      else:
        result = s.ast
    of skProc, skFunc, skMethod:
      result = n
    of skParam:
      if s.typ != nil and s.typ.kind == tyTypeDesc:
        result = newSymNodeTypeDesc(s, idgen, n.info)
      # XXX: static parameters should be expanded here (if resolved)
    of skType:
      # XXX gensym'ed symbols can come here and cannot be resolved. This is
      # dirty, but correct.
      if s.typ != nil:
        result = newSymNodeTypeDesc(s, idgen, n.info)
    of skGenericParam:
      if s.typ.kind == tyStatic:
        if s.typ.n != nil and tfUnresolved notin s.typ.flags:
          result = s.typ.n
          result.typ = s.typ.base
      elif s.typ.isIntLit:
        result = s.typ.n
      else:
        result = newSymNodeTypeDesc(s, idgen, n.info)
    else: discard
  of nkCharLit..nkNilLit:
    result = n
  of nkIfExpr:
    result = getConstIfExpr(n)
  of nkCallKinds:
    if n[0].kind != nkSym: return
    var s = n[0].sym
    if s.kind != skProc and s.kind != skFunc: return
    try:
      case s.magic
      of mNone:
        # If it has no sideEffect, `evalAtCompileTime` should evaluate it
        return
      of mLow:
        if skipTypes(n[1].typ, abstractVarRange).kind in tyFloat..tyFloat64:
          result = newFloatNodeT(firstFloat(n[1].typ), n, g)
        else:
          result = newIntNodeT(firstOrd(g.config, n[1].typ), n, idgen, g)
      of mHigh:
        if skipTypes(n[1].typ, abstractVar+{tyUserTypeClassInst}).kind notin
            {tySequence, tyString, tyCstring, tyOpenArray, tyVarargs}:
          if skipTypes(n[1].typ, abstractVarRange).kind in tyFloat..tyFloat64:
            result = newFloatNodeT(lastFloat(n[1].typ), n, g)
          else:
            result = newIntNodeT(lastOrd(g.config, skipTypes(n[1].typ, abstractVar)), n, idgen, g)
        else:
          let a = getArrayConstr(n[1], g)
          if a.kind == nkBracket:
            # we can optimize it away:
            result = newIntNodeT(toInt128(a.len-1), n, idgen, g)
      of mLengthOpenArray:
        let a = getArrayConstr(n[1], g)
        result =
          if a.kind == nkBracket:
            # we can optimize it away! This fixes the bug ``len(134)``.
            newIntNodeT(toInt128(a.len), n, idgen, g)
          elif allConst:
            evalOp(s.magic, n, n[1], nil, nil, idgen, g)
          else:
            nil
      of mLengthArray:
        # It doesn't matter if the argument is const or not for mLengthArray.
        # This fixes bug #544.
        result = newIntNodeT(lengthOrd(g.config, n[1].typ), n, idgen, g)
      of mSizeOf:
        result = foldSizeOf(g.config, n, nil)
      of mAlignOf:
        result = foldAlignOf(g.config, n, nil)
      of mOffsetOf:
        result = foldOffsetOf(g.config, n, nil)
      of mConStrStr:
        if allConst:
          result = foldConStrStr(m, n, idgen, g)
      of mIs:
        # The only kind of mIs node that comes here is one depending on some
        # generic parameter
        let
          t1 = n[1].typ.skipTypes({tyTypeDesc})
          t2 = n[2].typ

        # FIXME: this mirrors how ``vmgen`` previously folded the ``mIs``
        #        operation, and before that, how the VM implemented it --
        #        but it's incorrect. A ``mIs`` only reaches here because
        #        expression ``T is B`` where ``T`` depends on a generic
        #        parameter is assigned a ``bool`` type when it's first
        #        encountered, leading to the expression not reaching ``semIs``
        #        again (which would have otherwise folded it into a bool
        #        literal correctly)

        let match = if t2.kind == tyUserTypeClass: true
                    else: sameType(t1, t2)

        result = newIntNodeT(toInt128(ord(match)), n, idgen, g)
      else:
        if allConst:
          result = evalOp(s.magic, n, fold2(n, 1, g), fold2(n, 2, g), fold2(n, 3, g), idgen, g)
    except OverflowDefect:
      result = g.config.newError(n, PAstDiag(kind: adSemFoldOverflow))
    except DivByZeroDefect:
      result = g.config.newError(n, PAstDiag(kind: adSemFoldDivByZero))
  of nkAddr:
    result = n
  of nkBracket, nkCurly, nkTupleConstr, nkRange:
    result = n
  of nkObjConstr:
    # XXX: currently not supported because of a shortcoming of both
    #      ``vmcompilerserdes``
    discard
  of nkChckRangeF, nkChckRange64, nkChckRange:
    # XXX: these only have to be supported here because of unsanitized macro
    #      output. In normal AST, the nodes wouldn't exist when constant
    #      folding happens
    if leValueConv(n[1], n[0]) and leValueConv(n[0], n[2]):
      # a <= x and x <= b
      result = foldConv(n, n[0], idgen, g, check=false)
    else:
      result = g.config.newError(n,
                                 PAstDiag(kind: adSemInvalidRangeConversion))
  of nkHiddenStdConv, nkHiddenSubConv, nkConv:
    result = foldConv(n, n[1], idgen, g, check=true)
  of nkDerefExpr, nkHiddenDeref:
    if n[0].kind == nkNilLit:
      result = nil  # xxx: `nkNilLit` should generate an error; fix the code
                    #      that generates the obviously wrong deref
  of nkCast:
    if n.typ != nil and n.typ.kind in NilableTypes:
      # we allow compile-time 'cast' for pointer types:
      result = modify(n[1])
      result.typ = n.typ
  of nkBracketExpr:
    result = foldArrayAccess(n, g)
  of nkDotExpr:
    result = foldFieldAccess(n, g)
  of nkCheckedFieldExpr:
    # if a field-access is fully constant, the check is unnecessary, so we
    # fold it away
    result = n[0]
  else:
    discard

proc foldAst(m: PSym, n: PNode, idgen: IdGenerator, g: ModuleGraph): Folded

func root(n: PNode): PNode =
  ## Returns the constant at the root of the constant expression, or 'nil'.
  var n {.cursor.} = n
  while true:
    case n.kind
    of nkBracketExpr, nkDotExpr:
      n = n[0]
    of nkCallKinds:
      if n[0].sym.magic == mArrToSeq:
        n = n[1]
      else:
        break
    else:
      break

  if n.kind == nkSym and n.sym.kind == skConst:
    n
  else:
    nil

proc foldConstExprAux(m: PSym, n: PNode, idgen: IdGenerator, g: ModuleGraph,
                      wantValue: bool): Folded =
  ## Folds the sub-expressions of `n` and, if possible, `n` itself. If
  ## `wantValue` is 'true', statements part of the expression are not
  ## processed and constants are always inlined, regardless of complexity.
  ##
  ## For simplicity, `n` doesn't have to be an expression.
  result = Folded(node: n, allConst: true) # start as all const

  if nfAllConst in n.flags and not wantValue:
    # nothing to do
    return

  const Special = {nkElifBranch, nkElse, nkElifExpr, nkElseExpr,
                   nkExprColonExpr}

  # first step: fold the sub-expressions (if `n` is an expression itself)
  case n.kind
  of nkEmpty, nkLiterals, nkNimNodeLit, nkNilLit:
    discard "atoms that are constant"
  of nkTypeOfExpr:
    # XXX: could be folded into an ``nkType`` here...
    discard
  of nkSym:
    discard "constness decided when evaluating"
  of nkError:
    result.allConst = false
    result.hasError = true
  of nkCast, nkConv, nkHiddenStdConv, nkHiddenSubConv:
    # the first slot only holds the type, which we don't need to traverse
    # into / fold
    result.addConst n[0]
    result.add foldConstExprAux(m, n[1], idgen, g, wantValue)
  of nkCheckedFieldExpr:
    # only the first sub-node is relevant
    result.add foldConstExprAux(m, n[0], idgen, g, wantValue)
    for i in 1..<n.len:
      result.addConst n[i]
  of nkDotExpr:
    # don't traverse into the field node
    result.add foldConstExprAux(m, n[0], idgen, g, wantValue)
    result.addConst n[1]
  of nkObjConstr:
    result.addConst n[0] # skip the type slot
    for i in 1..<n.len:
      result.add foldConstExprAux(m, n[i], idgen, g, wantValue)
  of nkStmtListExpr:
    if stupidStmtListExpr(n):
      # special rule: collapse empty statement-list expressions
      return foldConstExprAux(m, n[^1], idgen, g, wantValue)
    else:
      result.allConst = false
      if not wantValue:
        for it in n.items:
          result.add foldAst(m, it, idgen, g)
  of nkBracket, nkCurly, nkTupleConstr, nkRange, nkHiddenDeref, nkDerefExpr,
     nkBracketExpr, nkCallKinds, nkIfExpr, nkElifExpr, nkElseExpr, nkElse,
     nkElifBranch, nkAddr:
    for it in n.items:
      result.add foldConstExprAux(m, it, idgen, g, wantValue)

    if n.kind in Special:
      return
  of nkExprColonExpr:
    # comes here from tuple/object constructions. Only fold the expression
    # and then return
    result.addConst n[0]
    result.add foldConstExprAux(m, n[1], idgen, g, wantValue)
    return
  of {low(TNodeKind)..high(TNodeKind)} - Evaluateable - Special:
    # this is either something statement-like or an expression that's not
    # supported
    if not wantValue:
      result = foldAst(m, n, idgen, g)
    result.allConst = false
    return

  if result.hasError:
    # don't attempt folding if the AST contains errors
    return

  if not result.allConst and n.kind notin nkCallKinds:
    # any of operands are not constant expression -> cannot be evaluated.
    # Calls are an exception, because some magics are folded even if the
    # arguments are not constant
    return

  # second step: use AST-based expression evaluation
  var e = getConstExpr(m, result.node, result.allConst, idgen, g)
  if e.isError:
    # there was an error during folding
    result = Folded(node: e, hasError: true)
  elif e != nil:
    # success!
    if not wantValue:
      # if a value is not preferred, don't fold expressions where doing so
      # would result in complex constants being inlined. In addition, don't
      # create non-empty ``seq`` literals
      let
        x = result.node
        r = root(x)
      if r != nil and dontInlineConstant(r, e):
        e = x

    if e.kind != nkSym and not isConstExpr(e):
      # mark non-symbol expression as constant. For symbols, it would just
      # introduce an unnecessary copy for no benefit
      e = modify(e)
      e.flags.incl nfAllConst

    # the result of a successfully evaluated expression is guaranteed to be
    # constant
    result.allConst = true
    result.node = e
  else:
    # evaluation failed -> it's not constant not a constant expression
    result.allConst = false

proc foldAst(m: PSym, n: PNode, idgen: IdGenerator, g: ModuleGraph): Folded =
  ## Folds all constant expression in the statement or expression `n`.
  case n.kind
  of Evaluateable:
    result = foldConstExprAux(m, n, idgen, g, wantValue = false)
  of callableDefs, nkTypeSection, nkConstSection, nkMixinStmt, nkBindStmt,
     nkPragma, nkImportStmt, nkExportStmt, nkFromStmt, nkImportExceptStmt,
     nkBreakStmt, nkContinueStmt:
    # skip declarative nodes and control-flow statements that don't contain
    # fold-able expressions
    result = Folded(node: n, allConst: false)
  of nkStmtList, nkIfStmt, nkCaseStmt, nkWhileStmt, nkWhenStmt, nkTryStmt,
     nkDefer, nkLetSection, nkVarSection, nkYieldStmt, nkReturnStmt,
     nkDiscardStmt, nkRaiseStmt, nkAsmStmt, nkAsgn, nkFastAsgn, nkFinally,
     nkElifBranch, nkElse, nkOfBranch, nkHiddenAddr:
    # something that's either a statement or not evaluatable. We still
    # want to process the subnodes.
    result = Folded(node: n, allConst: false)
    for it in n.items:
      result.add foldAst(m, it, idgen, g)

  of nkPragmaBlock, nkBlockStmt, nkBlockExpr:
    result = fromAst(n, n.len - 1)
    result.add foldAst(m, n[^1], idgen, g)
  of nkForStmt:
    # don't process the symbol slots
    result = fromAst(n, n.len - 2)
    result.add foldAst(m, n[^2], idgen, g)
    result.add foldAst(m, n[^1], idgen, g)
  of nkIdentDefs, nkVarTuple, nkExceptBranch:
    # don't process the symbol slots
    result = fromAst(n, n.len - 1)
    result.add foldAst(m, n[^1], idgen, g)
  else:
    # XXX: type AST reaches here, but ideally this catch-all branch
    #      wouldn't be needed
    result = Folded(node: n, allConst: false)

proc foldInAst*(m: PSym, n: PNode, idgen: IdGenerator, g: ModuleGraph): PNode =
  ## Performs constant folding on all expressions appearing in the statement or
  ## expression `n`.
  let f = foldAst(m, n, idgen, g)
  if f.hasError:
    result = g.config.wrapError(f.node)
  else:
    result = seal(f.node)

proc foldConstExpr*(m: PSym, n: PNode, idgen: IdGenerator, g: ModuleGraph): PNode =
  ## Attempts to fold the given expression. If unsuccessful, returns 'nil',
  ## the folded expression otherwise.
  let f = foldConstExprAux(m, n, idgen, g, wantValue = true)
  if f.allConst:
    result = seal(f.node)
  elif f.hasError:
    result = g.config.wrapError(f.node)
  else:
    result = nil
