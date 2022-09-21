
type CopyProc = proc (dst: pointer, src: pointer, shallow: bool) {.nimcall, benign, tags: [], raises: [].}

proc copySeq(dest: PPointer, src: PGenericSeq, mt: PNimType, copy: CopyProc, shallow: bool) {.compilerproc.} =
  let src = src
  if src == nil or shallow or (src.reserved and seqShallowFlag) != 0:
    # this can happen! nil sequences are allowed
    if shallow or (src != nil and (src.reserved and seqShallowFlag) != 0):
      echo "shallow"

    unsureAsgnRef(dest, src)
    return

  if copy == nil:
    let ss = nimNewSeqOfCap(mt, src.len)
    cast[PGenericSeq](ss).len = src.len
    unsureAsgnRef(dest, ss)

    let dst = cast[PGenericSeq](dest[])
    copyMem(dataPointer(dst, mt.base.align),
            dataPointer(src, mt.base.align),
            src.len *% mt.base.size)
  else:
    unsureAsgnRef(dest, newSeq(mt, src.len))
    let dst = cast[PGenericSeq](dest[])
    for i in 0..src.len-1:
      copy(
        dataPointer(dst, mt.base.align, mt.base.size, i),
        dataPointer(src, mt.base.align, mt.base.size, i),
        shallow)

proc assignString(dest, src: pointer, shallow: bool) {.compilerproc.} =
  let
    x = cast[PPointer](dest)
    s2 = cast[PPointer](src)[]

  if s2 == nil or shallow or (
      cast[PGenericSeq](s2).reserved and seqShallowFlag) != 0:
    unsureAsgnRef(x, s2)
  else:
    unsureAsgnRef(x, copyString(cast[NimString](s2)))

proc genericRefAssign(dest, src: pointer, shallow: bool) {.compilerproc, nimcall.} =
  unsureAsgnRef(cast[PPointer](dest), cast[PPointer](src)[])

proc destroyRefNoCycle(p: pointer) {.compilerproc, benign, tags: [], nimcall.} =
  {.cast(tags: []).}:
    #nimGCunrefNoCycle(cast[PPointer](p)[])
    unsureAsgnRef(cast[PPointer](p), nil)

proc destroyRef(p: pointer) {.compilerproc.} =
  unsureAsgnRef(cast[PPointer](p), nil)
  #nimGCunrefRC1(cast[PPointer](p)[])

proc objectInit(p: pointer, typ: PNimType) {.compilerproc.} =
  sysAssert(typ.init != nil, "'init' procedure missing!")
  typ.init(p)


strDesc.marker = proc (p: pointer, op: int) = discard
strDesc.destroy = destroyRefNoCycle
