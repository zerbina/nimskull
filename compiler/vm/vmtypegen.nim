## This module implements the `PType` to `VmType` translation. No duplicate
## types are allowed, making type comparison via ID (currently `PVmType`)
## possible.
##
## The `distinct` modifier is ignored (`distinct int` maps to the same type
## as just `int`) and named tuples are treated as unnamed tuples.

import
  compiler/ast/[
    ast_types,
    ast_query,
    ast,
    reports,
    types
  ],
  compiler/front/[
    options
  ],
  compiler/utils/[
    idioms,
    containers
  ],
  compiler/vm/[
    vmdef,
    vmtypes
  ],

  std/[
    hashes,
    tables
  ]

import std/options as soptions

type
  TypeTableEntry = tuple[hcode: int, typ: VmTypeId]
  TypeTable = object
    ## A partial hash-table overlay for `TypeInfoCache.types`. Not all types
    ## present in the latter need to be present in the table
    data*: seq[TypeTableEntry]
    counter*: int

  TypeTranslationState* = object
    ## Encapsulates all state needed for RTTI generation, such as various
    ## caches and other acceleration structures.
    cache: Table[ItemId, VmTypeId] ## `PType`-id -> `PVmType` mappings

    structs: TypeTable
      ## type-structure-based cache for types

    staticInfo: array[AtomKind, tuple[size, align: uint8]]
      ## size and alignment information for atoms where this information is
      ## the same for every instance

    rootRef*: VmTypeId
      ## the VM type corresponding to ``ref RootObj``.
      # XXX: this is a temporary workaround, the type cache shouldn't need to
      #      know nor care about ``RootObj``. Can be removed once closure types
      #      are lowered earlier
    rttiType*: Option[VmTypeId]
      ## the type to use for the RTTI field in objects

proc initTypeGen*(): TypeTranslationState =
  template pair(size: uint8, align: uint8): untyped =
    (uint8(size), uint8(align))

  result.staticInfo = [
    akVoid: pair(0, 0),
    akInt: pair(0, 0),
    akFloat: pair(0, 0),
    akPtr: pair(8, 3),
    akRef: pair(8, 3),
    akProc: pair(8, 3),
    akSet: pair(0, 0),
    akString: pair(16, 3),
    akSeq: pair(16, 3),
    akForeign: pair(8, 3),
    akRecord: pair(0, 0),
    akUnion: pair(0, 0),
    akArray: pair(0, 0),
    akFlexArray: pair(0, 0)
  ]

func hash(types: VmTypeEnv, t: VmType): Hash =
  ## Creates a hash over the fields of `t` that are relevant for structural
  ## types
  let h = hash(t.kind)
  let body =
    case t.kind
    of akSeq, akPtr, akRef, akFlexArray:   hash(t.a)
    of akSet:                 hash(t.a)
    of akProc, akRecord:
      var r = 0
      for i in t.a..<t.b:
        r = r !& hash(types.fields[i])
      r
    of akArray:
      hash(types.fields[t.a])
    of akInt, akFloat:
      hash(t.size) !& hash(t.a)
    of akVoid, akString, akForeign:
      0
    of akUnion:
      unreachable()

  result = !$(h !& body)

func compare(types: VmTypeEnv, a, b: VmType): bool =
  ## Compares the fields of `a` and `b` that are relevant for structural types
  if a.kind != b.kind:
    return false

  template cmpField(n): untyped = a.n == b.n

  # TODO: consider size and alignment

  case a.kind
  of akSeq, akPtr, akRef, akSet, akFlexArray:
    cmpField(a)
  of akProc, akRecord:
    if a.len != b.len:
      return false

    for i in a.a..<a.b:
      if types.fields[i] != types.fields[i - a.a + b.a]:
        return false

    true
  of akArray:
    types.fields[a.a] == types.fields[b.a]
  of akInt, akFloat:
    cmpField(size) and cmpField(a)
  of akVoid, akString, akForeign:
    true
  of akUnion:
    unreachable()

const skipTypeSet = abstractRange+{tyEnum}-{tyTypeDesc}

# ------------ TypeTable implementation ------------

template maxHash(t: TypeTable): int = t.data.high

func mustRehash(len, counter: int): bool {.inline.} =
  assert(len > counter)
  result = (len * 2 < counter * 3) or (len - counter < 4)

template isFilled(m: TypeTableEntry): bool = m.typ != 0

template nextTry(i, max: int): int =
  (i + 1) and max

func enlarge(tbl: var TypeTable) =
  ## Grows and re-hashes the table
  var n = newSeq[TypeTableEntry](tbl.data.len * 2)
  swap(n, tbl.data)
  for old in n.items:
    if old.isFilled:
      var j = old.hcode and maxHash(tbl)
      while tbl.data[j].isFilled:
        j = nextTry(j, maxHash(tbl))
      tbl.data[j] = old

func getOrIncl(types: var VmTypeEnv, tbl: var TypeTable,
               h: Hash, t: sink VmType): (VmTypeId, bool) =
  ## Returns the ID of structural type `t` and whether it existed prior to
  ## this operation. If the type is not in `types` yet, it is first added and
  ## also registered with `tbl`
  var i = h and maxHash(tbl)
  if tbl.data.len > 0:
    while (let m = tbl.data[i]; m.isFilled):
      if m.hcode == h and compare(types, types.types[m.typ], t):
        return (m.typ, true)
      i = nextTry(i, maxHash(tbl))

    # no matching entry found
    if mustRehash(tbl.data.len, tbl.counter):
      enlarge(tbl)
      i = h and maxHash(tbl)
      # find the first empty slot
      while (let m = tbl.data[i]; m.typ != 0):
        i = nextTry(i, maxHash(tbl))

  else:
    tbl.data.setLen(16) # needs to be a power-of-two
    i = h and maxHash(tbl)

  # add the type to the `types` list
  let id = types.types.add(t)

  # fill table entry
  tbl.data[i] = (h, id)
  inc tbl.counter
  result = (id, false)

# ------------ end ------------

type GenClosure* = object
  tmpFields: seq[Field]

  conf: ConfigRef
  typesPtr: ptr VmTypeEnv

template types(x: GenClosure): VmTypeEnv =
  x.typesPtr[]

proc genTuple(c: var TypeTranslationState, t: PType, cl: var GenClosure): VmType
proc genObject(c: var TypeTranslationState, t: PType, cl: var GenClosure): VmType

proc addUnique(cl: var GenClosure, c: var TypeTranslationState, t: sink VmType): VmTypeId =
  let (id, _) = cl.types.getOrIncl(c.structs, hash(cl.types, t), t)
  result = id

proc popRecord(cl: var GenClosure, size: uint32, start: int): VmType =
  var flags = {vtfDataOnly} # until proven otherwise
  for i in start..<cl.tmpFields.len:
    if vtfDataOnly notin cl.types[cl.tmpFields[i].typ].flags:
      flags.excl vtfDataOnly
      break

  result = VmType(kind: akRecord, size: size, flags: flags, a: cl.types.fields.len.uint32, b: uint32(cl.types.fields.len + (cl.tmpFields.len - start)))
  cl.types.fields.add cl.tmpFields.toOpenArray(start, cl.tmpFields.high)
  cl.tmpFields.setLen(start)

proc genType(c: var TypeTranslationState, t: PType, cl: var GenClosure;
             noClosure = false): VmTypeId =
  ## The heart of `PType` -> `VmType` translation. Looks up or creates types
  ## and adds mappings to `lut` if they don't exist already.
  ##
  ## If `noClosure` is 'true', a proc type with ``.closure`` calling
  ## convention is treated as a procedure type instead of a closure.
  let t = t.skipTypes(skipTypeSet)
  result = c.cache.getOrDefault(t.itemId, VoidType)
  if result != VoidType:
    return

  let start = cl.tmpFields.len # remember how many temporary fields there are
  var res: VmType

  case t.kind
  of tyVoid:
    res = VmType(kind: akVoid)
  of tyInt..tyInt64, tyBool:
    # FIXME: the alignment computation is wrong
    res = VmType(kind: akInt, size: uint32 getSize(cl.conf, t), align: getAlign(cl.conf, t).uint8, a: 1)
  of tyUInt..tyUInt64, tyChar:
    res = VmType(kind: akInt, size: uint32 getSize(cl.conf, t), a: 0)
  of tyFloat..tyFloat64:
    res = VmType(kind: akFloat, size: uint32 getSize(cl.conf, t))
  of tyVar, tyLent:
    if t[0].skipTypes(skipTypeSet).kind == tyOpenArray:
      return genType(c, t[0], cl)
    else:
      res = VmType(kind: akPtr, a: genType(c, t[0], cl).uint32)
  of tyPtr:
    res = VmType(kind: akPtr, a: genType(c, t[0], cl).uint32)
  of tyRef:
    if t.sym != nil and t.sym.magic == mPNimrodNode:
      res = VmType(kind: akForeign)
    else:
      let elem = genType(c, t[0], cl)
      cl.tmpFields.add Field(off: 0, typ: cl.addUnique(c, VmType(kind: akInt, size: 8, align: 3, a: 0)))
      # TODO: use proper offset that respects element's alignment
      cl.tmpFields.add Field(off: 8, typ: elem)
      let content = cl.types.types.add(cl.popRecord(8 + cl.types[elem].size, cl.tmpFields.len - 2))

      res = VmType(kind: akRef, a: genType(c, t[0], cl).uint32, b: content)
  of tyTypeDesc:
    # stored as a NimNode
    res = VmType(kind: akForeign)
  of tySequence:
    res = VmType(kind: akSeq, a: genType(c, t[0], cl).uint32)
  of tyString, tyCstring:
    res = VmType(kind: akString, a: genType(c, t[0], cl).uint32)
  of tyPointer:
    # use the 'void' type as the target type. The exact type doesn't matter,
    # we only need *some* type
    res = VmType(kind: akPtr, a: cl.addUnique(c, VmType(kind: akVoid)))
  of tyOpenArray, tyVarargs:
    let elem = genType(c, t[0], cl)
    let x = cl.addUnique(c, VmType(kind: akInt, size: 8, align: 3, a: 1))
    cl.tmpFields.add Field(off: 0, typ: x)
    let pt = cl.addUnique(c, VmType(kind: akPtr, size: 8, align: 3, a: elem))
    cl.tmpFields.add Field(off: 8, typ: pt)
    res = VmType(kind: akRecord, flags: {vtfDataOnly}, size: 16, align: 3)
  of tyProc:
    if t.callConv == ccClosure and not noClosure:
      # a closure is represented as a ``tuple[prc: proc, env: RootRef]``.
      # Manually create one.
      let prcTyp = c.genType(t, cl, noClosure=true)
      # do *not* elide the temporary, genType can modify `cl`!
      cl.tmpFields.add Field(off: 0, typ: prcTyp)
      cl.tmpFields.add Field(off: 8, typ: c.rootRef)

      res = VmType(kind: akRecord, size: 16, align: 3)
    else:
      if t[0].isEmptyType():
        cl.tmpFields.add Field(off: 0, typ: VoidType)
      else:
        let typ = c.genType(t[0], cl)
        if cl.types[typ].kind notin {akInt, akFloat, akProc, akRef, akPtr, akForeign}:
          cl.tmpFields.add Field(off: 0, typ: VoidType)

        cl.tmpFields.add Field(off: 0, typ: typ)

      for i in 1..<t.len:
        if t[i].kind notin {tyStatic, tyTypeDesc}:
          cl.tmpFields.add Field(off: 0, typ: c.genType(t[i], cl))

      res = VmType(kind: akProc)
  of tyObject:
    # create and cache the RTTI instance first. If another type for which
    # RTTI is generated during the traversal looks up the type, it gets
    # the cached ID and the cycle is thus broken
    result = cl.types.types.add VmType(kind: akRecord, size: getSize(cl.conf, t).uint32)
    c.cache[t.itemId] = result
    res = genObject(c, t, cl)
    cl.types.types[result] = res
    return
  of tyTuple:
    res = genTuple(c, t, cl)
  of tyArray:
    let L = toInt(lengthOrd(cl.conf, t))
    if L == 0:
      res = VmType(kind: akInt, size: 1, align: 1, a: 0)
    else:
      # XXX: the length might be cut off
      let elem = genType(c, elemType(t), cl)
      cl.tmpFields.add Field(off: L.uint32, typ: elem)
      res = VmType(kind: akArray, flags: cl.types[elem].flags, size: getSize(cl.conf, t).uint32)
  of tySet:
    # XXX: for now `set`s are separate atoms, but they could be represented
    #      via `akInt` and `akArry` similar to how the C backend does it.
    #      This would first require some language specification regarding
    #      static-/dynamic-type compatibility however.

    let L =
      if t[0].kind != tyEmpty: toUInt32(lengthOrd(cl.conf, t[0]))
      else: 0

    res = VmType(kind: akSet, a: uint32 L)

    # Calculate the size and alignment for the underlying storage
    (res.size, res.align) =
      if L <= 8:    (1'u32, 0'u8)
      elif L <= 16: (2'u32, 1'u8)
      elif L <= 32: (4'u32, 2'u8)
      elif L <= 64: (8'u32, 3'u8)
      else: (((L + 7) and (not 7'u32)) div 8, 3'u8)
  of tyUntyped:
    # XXX: this is a horrible, horrible workaround for the insanity that is
    #      getAst
    # let elem = cl.addUnique(c, VmType(kind: akForeign, size: 8, align: 3))
    # res = VmType(kind: akSeq, a: elem)
    discard
  of tyUncheckedArray:
    let elem = genType(c, elemType(t), cl)
    res = VmType(kind: akFlexArray, size: 1, align: cl.types[elem].align, a: elem)
  else:
    unreachable(t.kind)

  if res.kind in {akInt, akFloat, akProc, akPtr, akSet, akFlexArray}:
    res.flags.incl vtfDataOnly

  let before = cl.types.fields.len
  if start < cl.tmpFields.len:
    res.a = before.uint32
    res.b = res.a + uint32(cl.tmpFields.len - start)
  # tentatively add the new fields to the environment; the hash/compare logic
  # depends on it
  cl.types.fields.add cl.tmpFields.toOpenArray(start, cl.tmpFields.high)
  cl.tmpFields.setLen(start)

  if res.size == 0:
    # fill with the static information
    let (size, align) = c.staticInfo[res.kind]
    res.size = size
    res.align = align

  let (id, existed) = cl.types.getOrIncl(c.structs, hash(cl.types, res), res)
  if existed:
    # remove the temporary fields again
    cl.types.fields.setLen(before)

  result = id

  # speed up future calls to genType
  if t.kind != tyProc:
    c.cache[t.itemId] = result

proc align(offset: uint32, a: BiggestInt): uint32 =
  let a = uint32 a
  (offset + a - 1) and not(a - 1)

proc addTmpField(c: var TypeTranslationState, offset: var uint32, t: PType, cl: var GenClosure) =
  offset = align(offset, getAlign(cl.conf, t))
  let typ = genType(c, t, cl)
  cl.tmpFields.add Field(off: offset, typ: typ)
  offset += uint32 getSize(cl.conf, t)

proc genTuple(c: var TypeTranslationState, t: PType, cl: var GenClosure): VmType =
  ## Searches all previously created tuple types for a type equivalent to the
  ## `VmType` `t` maps to. If a matching `VmType` is found, it's id (`PVmType`)
  ## is returned. Otherwise, the new `VmType` is returned.
  var offset = 0'u32
  var flags = {vtfDataOnly} # until proven otherwise
  for i in 0..<t.len:
    addTmpField(c, offset, t[i], cl)
    if vtfDataOnly notin cl.types[cl.tmpFields[^1].typ].flags:
      flags.excl vtfDataOnly

  result = VmType(kind: akRecord, flags: flags, size: offset, align: uint8 getAlign(cl.conf, t))

proc genRecordNode(c: var TypeTranslationState, base: uint32, n: PNode,
                   cl: var GenClosure): uint32 =
  ## Recursively walks the given record node, populating `dest` with all
  ## record fields as well as branch walk-list information (if a record-case
  ## is present)
  case n.kind
  of nkSym:
    assert n.sym.offset >= 0
    let typ = genType(c, n.sym.typ, cl)
    assert cl.types[typ].kind != akVoid, $n.sym.typ.kind
    cl.tmpFields.add Field(off: n.sym.offset.uint32 - base, typ: typ)
    result = uint32(n.sym.offset + getSize(cl.conf, n.sym.typ)) - base
  of nkRecList:
    for x in n.items:
      result = genRecordNode(c, base, x, cl)
  of nkRecCase:
    let start = cl.tmpFields.len
    # discriminator
    let base = block:
      let typ = genType(c, n[0].sym.typ, cl)
      cl.tmpFields.add Field(off: n[0].sym.offset.uint32 - base, typ: typ)
      uint32(n[0].sym.offset + getSize(cl.conf, n[0].sym.typ))

    # a record-case uses its own RTTI item
    var selectors: seq[Selector]
    var size = getSize(cl.conf, n[0].sym.typ)
    var bodySize = 0'u32
    # there is a special "field" for tagged unions: the selector start.
    # Reserve a slot for it
    cl.tmpFields.setLen(start + 2)

    for i in 1..<n.len:
      let selstart = selectors.len
      for _, it in branchLabels(n[i]):
        if it.kind == nkRange:
          selectors.add Selector(isRange: true, branch: uint32(i - 1), val: toUInt64(getInt(it[0])))
          selectors.add Selector(isRange: true, branch: uint32(i - 1), val: toUInt64(getInt(it[1])))
        else:
          selectors.add Selector(isRange: false, branch: uint32(i - 1), val: toUInt64(getInt(it)))

      let start = cl.tmpFields.len
      let recsize = genRecordNode(c, base, n[i][^1], cl)
      # each branch is its own record type
      let typ = cl.types.types.add cl.popRecord(recsize, start)
      cl.tmpFields.add Field(off: uint32(selectors.len - selstart), typ: typ)

      bodySize = max(recsize, bodySize)

    # patch the special fields:
    cl.tmpFields[start + 1] = Field(off: cl.types.selectors.len.uint32, typ: cl.tmpFields[start].typ)

    cl.types.selectors.add selectors
    var typ = cl.popRecord(size.uint32 + bodySize, start) # TODO: not correct, given the special field
    typ.kind = akUnion
    let id = cl.types.types.add typ
    cl.tmpFields.add Field(off: n[0].sym.offset.uint32, typ: id)
    result = n[0].sym.offset.uint32 + bodySize
  else:
    unreachable()

proc genObject(c: var TypeTranslationState, t: PType, cl: var GenClosure): VmType =
  ##
  let start = cl.tmpFields.len

  if t[0] != nil:
    cl.tmpFields.add Field(off: 0, typ: genType(c, t[0], cl))
  elif not lacksMTypeField(t):
    if c.rttiType.isNone:
      # on-demand creation of the RTTI type. It's just an integer
      let body = VmType(kind: akInt, flags: {vtfDataOnly}, size: 8, align: 3)
      c.rttiType = some cl.addUnique(c, body)

    cl.tmpFields.add Field(off: 0, typ: c.rttiType.unsafeGet)
  elif t.n.len == 0:
    return VmType(kind: akInt, flags: {vtfDataOnly}, size: 1)

  let size = getSize(cl.conf, t) # make sure offsets are computed
  discard genRecordNode(c, 0, t.n, cl)
  result = cl.popRecord(size.uint32, start)

proc getOrCreate*(
  c: var TypeTranslationState,
  types: var VmTypeEnv,
  conf: ConfigRef,
  typ: PType,
  noClosure: bool): VmTypeId {.inline.} =
  ## Lookup or create the `VmType` corresponding to `typ`. If a new type is
  ## created, the `PType` -> `PVmType` mapping is cached
  var cl = GenClosure(conf: conf, typesPtr: addr types)
  result = genType(c, typ, cl, noClosure)
  assert types[result].size != 0, $typ.kind
  assert types[result].kind != akVoid

func lookup*(c: TypeTranslationState, typ: PType): Option[VmTypeId] =
  ## Searches the cache for a `VmType` matching the given `typ`. If one exists,
  ## it's returned, otherwise, `none` is returned
  let id = c.cache.getOrDefault(typ.skipTypes(skipTypeSet).itemId, VoidType)
  if id == VoidType: none(VmTypeId)
  else:              some(id)

proc initRootRef*(env: var VmTypeEnv, c: var TypeTranslationState,
                  config: ConfigRef, root: VmTypeId) =
  ## Sets up the ``rootRef`` field for `c`. `root` must be the ``PType`` for
  ## the ``RootObj`` type.
  var typ = VmType(kind: akRef, a: root)
  (typ.size, typ.align) = c.staticInfo[akRef]

  let (id, _) = env.getOrIncl(c.structs, hash(env, typ), typ)
  c.rootRef = id

proc createProcType*(c: var TypeTranslationState, config: ConfigRef, env: var VmTypeEnv, typ: PType): VmTypeId =
  ## Creates a proc
  var cl = GenClosure(typesPtr: addr env, conf: config)
  let typ = c.genType(typ, cl)
  let start = env.fields.len
  env.fields.add Field(typ: typ)
  var t = VmType(kind: akProc, size: 8, align: 3, a: uint32(start), b: uint32(start + 1))
  let (id, exists) = env.getOrIncl(c.structs, hash(env, t), t)
  result = id
  if exists:
    env.fields.setLen(start)
