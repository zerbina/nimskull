## Mirrors the behaviour of the old ``seq`` implementation from
## ``system/sysstr.nim``, with the difference that the simpler version of
## the RTTI is used.
##
## Included in ``system.nim``

proc growSeq(s: PGenericSeq, typ: PNimType, reserved: int): PGenericSeq =
  result = cast[PGenericSeq](newSeq(typ, reserved))
  copyMem(dataPointer(result, typ.base.align), dataPointer(s, typ.base.align), s.len * typ.base.size)
  # we're moving the contents of `s` to the new seq, so we have to set the
  # length of `s` to 0. The contents would exist in valid memory multiple
  # times otherwise (only items inside ``0..<s.len`` are considered valid
  # memory)
  s.len = 0

proc initItems(s: PGenericSeq, typ: PNimType, items: Slice[int]) =
  let init = typ.init
  if init != nil:
    for i in items.items:
      init(dataPointer(result, typ.elemAlign, typ.elemSize, i))

proc incrSeqV3(s: PGenericSeq, typ: PNimType): PGenericSeq {.compilerproc.} =
  ## Ensures that there is enough space for one more element. No
  ## initialization (via `typ.init`) is performed, as the new slot is assigned
  ## to immediately after the call to ``incrSeqV3``
  if s == nil:
    result = cast[PGenericSeq](newSeq(typ, 1))
    result.len = 0
  else:
    result = s
    if result.len >= result.space:
      let len = s.len
      result = growSeq(s, typ, resize(result.space))
      result.len = len

proc setLengthSeqV2(s: PGenericSeq, typ: PNimType, newLen: int): PGenericSeq {.
    compilerRtl.} =
  ## Shrinks or grows `s` of type `typ` to `newLen`
  if s == nil:
    result = cast[PGenericSeq](newSeq(typ, newLen))
    initItems(result, typ.base, 0..newLen-1)
  else:
    let
      elemSize = typ.base.size
      elemAlign = typ.base.align

    if s.space < newLen:
      # grow the capacity
      let len = s.len
      result = growSeq(s, typ, max(resize(s.space), newLen))
      initItems(result, typ.base, len..newLen-1)
    elif newLen < s.len:
      # shrink
      result = s

      let oldLen = s.len
      result.len = newLen

      # destroy all elements past `newLen`
      let destroy = typ.base.destroy
      if destroy != nil:
        for i in newLen..<oldLen:
          destroy(dataPointer(result, elemAlign, elemSize, i))

      zeroMem(dataPointer(result, elemAlign, elemSize, newLen), (oldLen-%newLen) *% elemSize)
    else:
      # grow
      result = s
      zeroMem(dataPointer(result, elemAlign, elemSize, result.len), (newLen-%result.len) *% elemSize)

      initItems(result, typ.base, result.len..newLen-1)

    result.len = newLen