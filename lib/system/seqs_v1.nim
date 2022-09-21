## Mirrors the behaviour of the old ``seq`` implementation from
## ``system/sysstr.nim``, with the difference that the simpler RTTI is used

proc growSeq(s: PGenericSeq, typ: PNimType, reserved: int): PGenericSeq =
  result = cast[PGenericSeq](newSeq(typ, reserved))
  copyMem(dataPointer(result, typ.base.align), dataPointer(s, typ.base.align), s.len * typ.base.size)
  # since we steal the content from 's', it's crucial to set s's len to 0.
  s.len = 0

proc incrSeqV3(s: PGenericSeq, typ: PNimType): PGenericSeq {.compilerproc.} =
  if s == nil:
    result = cast[PGenericSeq](newSeq(typ, 1))
    result.len = 0
  else:
    result = s
    if result.len >= result.space:
      let
        r = resize(result.space)
      result = cast[PGenericSeq](newSeq(typ, r))
      result.len = s.len
      copyMem(dataPointer(result, typ.base.align), dataPointer(s, typ.base.align), s.len * typ.base.size)
      # since we steal the content from 's', it's crucial to set s's len to 0.
      s.len = 0

proc setLengthSeqV2(s: PGenericSeq, typ: PNimType, newLen: int): PGenericSeq {.
    compilerRtl.} =
  if s == nil:
    result = cast[PGenericSeq](newSeq(typ, newLen))
  else:
      let elemSize = typ.base.size
      let elemAlign = typ.base.align
      if s.space < newLen:
        let len = s.len
        result = growSeq(s, typ, max(resize(s.space), newLen))
        let init = typ.base.init
        if init != nil:
          for i in len..<newLen:
            discard#init(dataPointer(result, elemAlign, elemSize, i))

      elif newLen < s.len:
        result = s

        let oldLen = result.len
        result.len = newLen

        # destroy all elements past `newLen`
        let destroy = typ.base.destroy
        if destroy != nil:
          for i in newLen..<oldLen:
            discard#destroy(dataPointer(result, elemAlign, elemSize, i))

        # XXX: does the comment below still apply? Maybe the ``zeroMem`` isn't
        #      necessary anymore now
        # XXX: zeroing out the memory can still result in crashes if a wiped-out
        # cell is aliased by another pointer (ie proc parameter or a let variable).
        # This is a tough problem, because even if we don't zeroMem here, in the
        # presence of user defined destructors, the user will expect the cell to be
        # "destroyed" thus creating the same problem. We can destroy the cell in the
        # finalizer of the sequence, but this makes destruction non-deterministic.
        zeroMem(dataPointer(result, elemAlign, elemSize, newLen), (oldLen-%newLen) *% elemSize)
      else:
        result = s
        zeroMem(dataPointer(result, elemAlign, elemSize, result.len), (newLen-%result.len) *% elemSize)

        let init = typ.base.init
        if init != nil:
          for i in result.len..<newLen:
            discard#init(dataPointer(result, elemAlign, elemSize, i))

      result.len = newLen