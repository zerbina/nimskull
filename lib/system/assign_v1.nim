## Implements the assignment logic of version-1 sequences and strings plus
## helper ``.compilerprocs`` related to the old-style RTTI -- both are
## only needed and used by the C code-generator.
## ``strDesc`` (the old-style RTTI object for ``string``) is also set-up here
##
## Included in ``system.nim``

type
  CopyProc = proc (dest: pointer, src: pointer, shallow: bool) {.nimcall, benign, tags: [], raises: [].}

# XXX: rename to `assignSeq`?
proc copySeq(dest: PPointer, src: PGenericSeq, mt: PNimType, copy: CopyProc, shallow: bool) {.compilerproc.} =
  ## If `shallow` is 'false', creates a new sequence in `dest` and copies over
  ## all items from `src`, using either an element-wise copy with the provided
  ## `copy` or, if `copy` is 'nil', by performing a blit copy.
  ##
  ## If `shallow` is 'true', only the ``ref`` is copied, so both source and
  ## destination will refer to the same (as in identity) sequence.

  # 'nil' sequence are allowed
  if src == nil or shallow or (src.reserved and seqShallowFlag) != 0:
    # do a shallow copy of the sequence, i.e. only copy the ``ref``
    unsureAsgnRef(dest, src)
    return

  if copy == nil:
    sysAssert(mt.base.destroy == nil, "the element type has a destructor but" &
              " seems to be missing an assignment operator")

    # if no dedicated copy/assginment procedure is present, it means that the
    # type contains no references and that a blit copy can be used
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
      copy(dataPointer(dst, mt.base.align, mt.base.size, i),
           dataPointer(src, mt.base.align, mt.base.size, i),
           shallow)

proc assignString(dest, src: pointer, shallow: bool) {.compilerproc.} =
  ## ``CopyProc``-adapter for string.
  let
    dest = cast[PPointer](dest)
    src = cast[ptr NimString](src)[]

  # 'nil' strings are allowed
  if src == nil or shallow or (src.reserved and seqShallowFlag) != 0:
    unsureAsgnRef(dest, src)
  else:
    unsureAsgnRef(dest, copyString(src))

proc genericRefAssign(dest, src: pointer, shallow: bool) {.compilerproc, nimcall.} =
  # Code-gen helper procedure that adapts ``unsureAsgnRef`` to the signature
  # expected by ``copySeq``
  unsureAsgnRef(cast[PPointer](dest), cast[PPointer](src)[])

proc objectInit(p: pointer, typ: PNimType) {.compilerproc.} =
  ## Code-gen helper. Calls the types' init procedure on the location pointed
  ## to by `p`
  sysAssert(typ.init != nil, "'init' procedure missing!")
  typ.init(p)

when declared(nimGCunrefRC1):
  # The destroy procedures are only needed for garbage collectors that use
  # some form of refcounting.
  #
  # They're also only applied to the elements of sequences, and since the
  # contents of a ``seq`` are known to be always located on the heap, we
  # can decrement the refcounter directly without having to go through
  # ``unsureAsgnRef``.

  proc destroyRefNoCycle(p: pointer) {.compilerproc, benign, tags: [], nimcall.} =
    let p = cast[PPointer](p)[]
    # when ``-d:useGcAssert`` is enabled, we'd get an "unlisted RootEffect"
    # compiler error without the cast
    {.cast(tags: []).}:
      if p != nil:
        nimGCunrefNoCycle(p)

  proc destroyRef(p: pointer) {.compilerproc.} =
    let p = cast[PPointer](p)[]
    if p != nil:
      nimGCunrefRC1(p)

  # set the destroy hook for the ``string`` type, so that they're properly
  # released when being used inside ``seq``s
  strDesc.destroy = destroyRefNoCycle

# strings don't contain any GC'ed memory, so the marker procedure is a no-op
strDesc.marker = proc (p: pointer, op: int) = discard