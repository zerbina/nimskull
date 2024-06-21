## Implements the deserialization of VM data into `PNode`-trees.

import
  compiler/ast/[
    ast_types,
    ast,
    astalgo,
    errorhandling,
    lineinfos,
    nimsets,
    types
  ],
  compiler/utils/[
    idioms
  ],
  compiler/front/[
    options
  ],
  compiler/vm/[
    vmaux,
    vmdef,
    # vmmemory,
    vmalloc,
    vmobjects,
    vmtypes,
  ],
  experimental/[
    results
  ]

from compiler/ast/trees import cyclicTree

const SkipSet = abstractRange + {tyStatic} - {tyTypeDesc}

type
  TCtx = object
    # pointers to immutable state:
    allocatorPtr: ptr VmAllocator
    typesPtr: ptr VmTypeEnv
    envPtr: ptr VmEnv
    config: ConfigRef

template allocator(c: TCtx): VmAllocator =
  c.allocatorPtr[]
template types(c: TCtx): VmTypeEnv =
  c.typesPtr[]

template wrongNode(t: PType): PNode =
  mixin info
  newNodeIT(nkEmpty, info, t)

proc deserialize(c: TCtx, loc: HostPointer, vt: VmTypeId, formal, t: PType, info: TLineInfo): PNode

#[
proc deserializeObject(c: TCtx, p: pointer, vt: PVmType, f, con: PType, info: TLineInfo): PNode
]#

proc deserializeRef(c: TCtx, p: VirtualAddr, vt: VmTypeId; f, con: PType, info: TLineInfo): PNode =
  ## Produces the construction AST for the `ref` value represented by `slot`.
  ## If the heap slot is inaccessible or its type not compatible with `vt`,
  ## an error is returned. For the 'nil' slot, a nil literal is returned.
  ##
  ## When `vt` is not ``noneType``, the value is deserialized as if it were of
  ## type `vt`. Otherwise the full value is deserialized.
  missing("refs")
  #[
  assert con.kind == tyRef

  let res = c.allocator.mapPointerToCell(p)
  if res.isSome:
    # it's a valid cell
    let base = con.base.skipTypes(abstractInst)
    if base.kind == tyObject
      if matches(vt, res.unsafeGet.typ):
        # the type's match, now deserialize
        c.deserializeObject(res.unsafeGet.p, res.unsafeGet, f, con.base.skipTypes(abstractInst), done)
      else:
        c.config.newError(wrongNode(f), PAstDiag(kind: adVmAccessTypeMismatch))
    else:
      c.config.newError(wrongNode(f), PAstDiag(kind: adVmUnsupportedNonNil,  unsupported: con))
  else:
    c.config.newError(wrongNode(f), PAstDiag(kind: adVmAccessOutOfBounds))
]#

proc deserialize(c: TCtx, p: HostPointer, vt: VmTypeId, formal: PType, info: TLineInfo): PNode {.inline.} =
  deserialize(c, p, vt, formal, formal.skipTypes(SkipSet), info)

proc deserializeTuple(c: TCtx, p: HostPointer, vt: VmTypeId; formal, ty: PType, info: TLineInfo): PNode =
  assert c.types[vt].kind == akRecord

  result = newNodeIT(nkTupleConstr, info, formal)
  result.sons.newSeq(c.types[vt].len)

  template deserializeField(o, t, nt): untyped =
    c.deserialize(p + o, t, nt, info)

  if ty.n != nil:
    # named tuple
    for i, f in fields(c.types, vt):
      result[i] = newTree(nkExprColonExpr,
        newSymNode(ty.n[i].sym), deserializeField(f.off, f.typ, ty[i]))
  else:
    # unnamed tuple
    for i, f in fields(c.types, vt):
      result[i] = deserializeField(f.off, f.typ, ty[i])

proc deserializeObject(c: TCtx,
  loc: HostPointer,
  vt: VmTypeId,
  start: var uint32,
  n: PNode, info: TLineInfo,
  dest: PNode) =
  template constrField(f, sym): untyped =
    let n = c.deserialize(loc + f.off, f.typ, sym.typ, info)
    nkExprColonExpr.newTreeI(info, newSymNode(sym), n)

  case n.kind
  of nkSym:
    dest.add constrField(c.types.fields[c.types[vt].a + start], n.sym)
    inc start
  of nkRecCase:
    let vt = c.types.fields[c.types[vt].a + start].typ
    dest.add constrField(c.types.fields[c.types[vt].a], n[0].sym)

    if dest[^1][1].kind != nkError:
      let val = getInt(dest[^1][1])
      let branch = selectBranch(val.toUInt, c.types, vt)
      if branch >= 0:
        deserializeObject(c, loc, c.types.branch(vt, branch), start, n[1 + branch][^1], info, dest)
      else:
        missing("error reporting")

    inc start # always move forward, even for errors
  of nkRecList:
    for i, it in n.pairs:
      deserializeObject(c, loc, vt, start, it, info, dest)
  else:
    unreachable(n.kind)

proc deserializeObject(c: TCtx, loc: HostPointer, vt: VmTypeId; f, con: PType; info: TLineInfo): PNode =
  assert con.kind == tyObject
  var dest = newNodeIT(nkObjConstr, info, f)
  dest.add newNodeIT(nkType, info, f)
  var start = 0'u32
  proc rec(c: TCtx, t: PType, dest: PNode) =
    if t[0] != nil:
      rec(c, t[0].skipTypes(skipPtrs), dest)

    deserializeObject(c, loc, vt, start, t.n, info, dest)
  rec(c, con, dest)
  result = dest

template safeSlice(a: VmAllocator, p: VirtualAddr, len: uint64): HostPointer =
  var content: HostPointer
  if checkmem(a, p, len, content):
    return
  content

proc deserializeArray(
  c: TCtx,
  m: HostPointer,
  count: int, eTyp: VmTypeId,
  formal, t: PType, info: TLineInfo): PNode =
  ## Doesn't set the resulting node's type. `f` is the formal array
  ## element type
  result = newNodeI(nkBracket, info, count)
  result.typ = formal

  let elem = elemType(t)

  var off = 0'u32
  for i in 0..<count:
    result[i] =
      c.deserialize(m + off, eTyp, elem, info)
    off += c.types[eTyp].size

proc load[T](x: HostPointer, typ: typedesc[T]; off = 0): T =
  copyMem(addr result, addr x[off], sizeof(T))

proc deserialize(c: TCtx, loc: HostPointer, vt: VmTypeId, formal, t: PType, info: TLineInfo): PNode =
  let s = c.types[vt].size

  template setResult(k: TNodeKind, f, v) =
    result = newNodeIT(k, info, formal)
    result.f = v

  template wrongNode(): PNode =
    ## For `newError`. There doesn't exist a "wrong node" here, so we're
    ## simply using an empty node instead
    newNodeIT(nkEmpty, info, formal)

  case t.kind
  of tyChar, tyUInt..tyUInt64:
    result = newIntTypeNode(cast[BiggestInt](loc.readUInt(s)), formal)
    result.info = info
  of tyBool, tyInt..tyInt64:
    result = newIntTypeNode(loc.readInt(s), formal)
    result.info = info
  of tyEnum:
    # the value is stored as the enum's underlying type
    result = deserialize(c, loc, vt, formal, t.lastSon, info)
  of tyFloat32:
    setResult(nkFloat32Lit, floatVal, loc.load(float32))
  of tyFloat64, tyFloat:
    setResult(nkFloat64Lit, floatVal, loc.load(float64))
  of tyCstring, tyString:
    let len = loc.load(int64)
    let p = loc.load(VirtualAddr, 8)
    if p != 0:
      var content: HostPointer
      if checkmem(c.allocator, p + 8, uint64(len), content):
        return c.config.newError(wrongNode(), PAstDiag(kind: adVmDerefAccessOutOfBounds))
      var str = newString(len)
      if len > 0:
        copyMem(addr str[0], content, len)
      setResult(nkStrLit, strVal, str)
    else:
      setResult(nkStrLit, strVal, "")
  of tyPtr, tyPointer, tyNil:
    if loc.load(VirtualAddr) == 0:
      result = newNodeIT(nkNilLit, info, formal)
    else:
      result = c.config.newError(
        wrongNode(),
        PAstDiag(kind: adVmUnsupportedNonNil, unsupported: t))
  of tyRef:
    if t.sym == nil or t.sym.magic != mPNimrodNode:
      # FIXME: cyclic references will lead to infinite recursion
      # result = deserializeRef(c, atom.refVal, vt.targetType, formal, t, info)
      discard
    else:
      let id = loc.rd(ForeignRef)
      # TODO: validate
      let node = c.allocator.lookup(id, PNode)

      if unlikely(cyclicTree(node)):
        result = c.config.newError(
          wrongNode(),
          PAstDiag(kind: adCyclicTree, cyclic: node))
      else:
        # XXX: not doing a full tree-copy here might lead to issues
        result = newTreeIT(nkNimNodeLit, info, formal): node

  of tyProc:
    let prcVal = loc.load(VmFunctionPtr, 0)
    if prcVal.isNil:
      result = newNodeIT(nkNilLit, info, formal)
    else:#if c.check(prcVal):
      let sym = c.envPtr.procs[int toFuncIndex(prcVal)].sym
      # TODO: ensure that the procedural types match (sameType should do)

      if t.callConv == ccClosure:
        # closures have an extra environment pointer
        let envPtr = loc.rd(VirtualAddr, 0)
        result = newTreeIT(nkClosure, info, formal)
        result.add newSymNode(sym, info)
        result.add:
          if envPtr == 0:
            newNodeI(nkNilLit, info)
          else:
            let t = getEnvParam(sym).typ
            c.deserializeRef(envPtr, VoidType, t, t, info)

      else:
        result = newSymNode(sym, info)
    # else:
    #    result = c.config.newError(wrongNode(), PAstDiag(kind: adVmAccessOutOfBounds))

  of tyObject:
    result = deserializeObject(c, loc, vt, formal, t, info)
  of tyTuple:
    result = deserializeTuple(c, loc, vt, formal, t, info)
  of tySequence, tyOpenArray, tyArray:
    case c.types[vt].kind
    of akArray:
      assert t.kind in {tyArray, tyOpenArray}
      let (count, typ) = c.types.unpackArray(vt)
      result = deserializeArray(c, loc,
        count.int, typ, formal, t,
        info)
    of akString, akSeq:
      assert t.kind in {tySequence, tyOpenArray}
      let len = loc.rd(int64, 0)
      let p = loc.rd(VirtualAddr, 8)
      if p != 0:
        let elem = c.types[vt].elem
        result = deserializeArray(c,
          safeSlice(c.allocator, p + 8, uint64(len * int64(c.types[elem].size))),
          len.int,
          elem,
          formal, t,
          info)
      else:
        result = newNodeIT(nkBracket, info, formal)
    else:
      unreachable(c.types[vt].kind)

  of tySet:
    result = toTreeSet(nil, toOpenArray(loc, 0, c.types[vt].size.int-1), formal, info)
  of tyVar, tyLent, tyUntyped, tyTyped, tyTypeDesc:
    # TODO: disallow in sem
    missing("reject compile-time border types in typeAllowed")
  else:
    unreachable()

  assert result.typ != nil, $t.kind

proc deserialize*(env: VmEnv, config: ConfigRef, p: HostPointer, typ: VmTypeId, asType: PType, info: TLineInfo): PNode =
  var c = TCtx(typesPtr: addr env.types, allocatorPtr: addr env.allocator, envPtr: addr env, config: config)
  deserialize(c, p, typ, asType, info)
