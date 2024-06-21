## Implements the various RTTI-based operations.
##
## Ideally, all of this would be implemented in bytecode, but compile-time
## code doesn't fully support hooks yet.

import
  compiler/ast/[
    ast_types,
    ast
  ],
  compiler/front/[
    options
  ],
  compiler/utils/[
    containers,
    idioms
  ],
  compiler/vm/[
    vmdef,
    vmalloc,
    vmtypes
  ]

import std/options as soptions

func reinterpretWrite[T](p: pointer, v: T) {.inline.} =
  copyMem(p, unsafeAddr v, sizeof T)

# TODO: think about endianness of the VM a bit. Right now it's the same
# as the host's, but maybe it should be the same as the target's instead?

template rd*[T](p: HostPointer, typ: typedesc[T]; off = 0): T =
  cast[ptr typ](cast[uint](p) + off)[]
template load*[T](p: HostPointer, typ: typedesc[T]; off = 0): T =
  cast[ptr typ](cast[uint](p) + off)[]

proc store*[T](dest: HostPointer, val: T) {.inline.} =
  copyMem(dest, addr val, sizeof(val))

proc store*[T](dest: HostPointer, val: T, a: uint32) {.inline.} =
  # TODO: endianess
  copyMem(dest, addr val, a)

func readUInt*(p: pointer, size: range[1..8]): uint64 =
  result = 0
  copyMem(addr result, p, size)

func readInt*(p: pointer, size: range[1..8]): int64 =
  result = 0
  copyMem(addr result, p, size)
  # sign-extend to the full width:
  let shift = 8 * (sizeof(BiggestInt) - size)
  result = (result shl shift) shr shift

template signExtended*(val, size: BiggestInt): untyped =
  ## Calculates sign-extended `x` without branching. `size` is the number of
  ## bytes `val` occupies.
  let lsh = 8 * (sizeof(val) - size)
  ashr(val shl lsh, lsh)

template `[]`(x: VmTypeEnv, i: VmTypeId): VmType =
  x.types[i]

# the type environment was checked
{.push checks: off.}

func selectBranch*(val: uint64, types: VmTypeEnv, typ: VmTypeId): int32 =
  var i = types.fields[types[typ].a + 1].off
  # go over all branches
  for f in (types[typ].a + 2)..<types[typ].b:
    let last = i + types.fields[f].off
    # go over the selector list
    while i <= last:
      let it = types.selectors[i]
      let match =
        if it.isRange:
          let a = it.val
          inc i
          val in a..types.selectors[i].val
        else:
          it.val == val

      if match:
        return int32(it.branch)

      inc i

  # no match
  result = -1

func decRef(dst: pointer, orig: VirtualAddr, a: var VmAllocator) =
  let dst = cast[ptr uint](dst)
  dec dst[]
  if dst[] == 0:
    a.deferred.add orig

func incRef(dst: pointer) =
  let dst = cast[ptr uint](dst)
  inc dst[]

template `+`*(a: HostPointer, b: uint): HostPointer =
  cast[HostPointer](addr a[b])

func inc(p: var HostPointer, x: uint) =
  p = p + x

template `==`*(a, b: VirtualAddr): bool =
  ord(a) == ord(b)

template checked(a: VmAllocator, p: VirtualAddr, len: uint64): HostPointer =
  var res: HostPointer
  if unlikely(checkmem(a, p, len, res)):
    return
  res

proc `-`*(a: VirtualAddr, b: uint64): VirtualAddr =
  VirtualAddr(a.uint64 - b)
proc `+`*(a: VirtualAddr, b: uint64): VirtualAddr =
  VirtualAddr(a.uint64 + b)

proc wr*[T](x: HostPointer, typ: typedesc[T], value: T; off = 0) =
  # converting `off` to uint is safe even if it's negative
  copyMem(addr x[off], addr value, sizeof(T))

proc allocVmString*(a: var VmAllocator, len: Natural): VirtualAddr {.inline.} =
  # +1 for the terminating '\0'
  let len = len + 1
  result = a.alloc0(uint(len) + 8) # use untyped memory
  a.translate(result).wr(int64, len) # capacity

proc newString*(a: var VmAllocator, dest: HostPointer, str: string) =
  dest.wr(int64, str.len)
  let p = allocVmString(a, str.len)
  dest.wr(VirtualAddr, p, 8)
  if str.len > 0:
    # copy the content:
    copyMem(addr a.translate(p)[8], addr str[0], str.len)

proc newSeqPayload*(a: var VmAllocator, len: int64, size: uint32): VirtualAddr =
  if len > 0:
    result = a.alloc(uint(len * size.int64) + 8)
    a.translate(result).wr(int64, len) # capacity

proc newSeq*(a: var VmAllocator, dest: VirtualAddr, len: int64, size: uint32) =
  let p = newSeqPayload(a, len, size)
  let dest = a.translate(dest)
  dest.wr(int64, len)
  dest.wr(VirtualAddr, p, 8)
  if len > 0:
    zeroMem(a.translate(p + 8), len * int64(size))

template check(cond: bool) =
  if unlikely(cond):
    when not defined(release):
      debugEcho "error at: ", instantiationInfo(-1)
    return true

func destroy*(loc: HostPointer, types: VmTypeEnv, typ: VmTypeId, a: var VmAllocator): bool =
  ## RTTI-based cleanup.
  # deallocating memory doesn't affect virtual->host mapping, so `loc` can be
  # a host pointer
  case types[typ].kind
  of akInt, akFloat, akPtr, akSet, akProc:
    discard "nothing to do"
  of akString:
    let p = loc.rd(VirtualAddr, 8)
    if p != VirtualAddr(0):
      check a.dealloc(p)

  of akSeq:
    let elem = types[typ].elem
    let p = loc.rd(VirtualAddr, 8)

    if p != VirtualAddr(0):
      let len = max(0, loc.rd(int64, 0))
      var content: HostPointer
      check checkmem(a, p + 8, uint64(len * int64(types[elem].size)), content)

      if vtfDataOnly notin types[elem].flags:
        for _ in 0..<len:
          check destroy(content, types, elem, a)
          inc content, types[elem].size

      check a.dealloc(p)

  of akRef:
    let val = loc.rd(VirtualAddr) - 8 # 8 for the refcount
    var content: HostPointer
    check checkmem(a, val, 8, content)
    decRef(content, val, a)
  of akForeign:
    let val = loc.rd(ForeignRef)
    if val.isNonNil:
      check not(check(a, val))
      decRef(a, val)
  of akRecord:
    if vtfDataOnly notin types[typ].flags:
      for _, f in fields(types, typ):
        check destroy(loc + f.off, types, f.typ, a)

  of akUnion:
    if vtfDataOnly notin types[typ].flags:
      let sel = types.fields[types[typ].a].typ
      let x = loc.readUInt(types[sel].size.int)
      let branch = selectBranch(x, types, typ)
      if branch >= 0:
        check destroy(loc + types[sel].size, types, types.branch(typ, branch), a)
      else:
        return true # error
  of akArray:
    if vtfDataOnly notin types[typ].flags:
      var p = loc
      let (count, elem) = types.unpackArray(typ)
      for i in 0..<count:
        check destroy(p, types, elem, a)
        inc p, types[elem].size
  of akVoid, akFlexArray:
    unreachable()


template `!=`*(x: VirtualAddr, n: typeof(nil)): bool =
  x.uint64 != 0

template `==`*(x: VirtualAddr, b: untyped): bool =
  x.uint64 == uint64(b)

proc validate(a: VmAllocator, start: VirtualAddr, len: uint): bool =
  var p: HostPointer
  result = checkmem(a, start, len, p)

template inc(a: VirtualAddr, by: uint) =
  uint64(a) = a.uint64 + by

proc copy*(dst, src: VirtualAddr, types: VmTypeEnv, typ: VmTypeId, a: var VmAllocator): bool =
  ## Performs a full copy from src to dst. Containers are fully copied too.
  # note: the destination and source pointer *can not* be host addresses,
  # since copying may causes allocations, which could change the virtual->host
  # mapping (i.e., the host address could become stale)
  template recurse(dst, src: VirtualAddr, typ: VmTypeId) =
    {.line.}:
      check copy(dst, src, types, typ, a)

  case types[typ].kind
  of akInt, akFloat, akPtr, akSet, akProc:
    copyMem(a.translate(dst), a.translate(src), types[typ].size)
  of akString, akSeq:
    let
      dstHost = a.translate(dst)
      srcHost = a.translate(src)
      slen = srcHost.rd(int64, 0)
      dp = dstHost.rd(VirtualAddr, 8)
      sp = srcHost.rd(VirtualAddr, 8)
      elem = types[typ].elem

    # echo "copy it: ", repr(sp), " dest: ", repr(dp), " | ", slen
    # do nothing if the payloads are equal
    if dp != sp:
      # clean up the destination first
      check destroy(dstHost, types, typ, a)

      var p: VirtualAddr
      if slen > 0:
        # create the new payload and copy the contents:
        p = newSeqPayload(a, slen, types[elem].size)
        check p == 0
        # ---- host addresses might have become stale ----
        var target = p + 8#dataPtr(p))
        check validate(a, sp + 8, uint(slen*int64(types[elem].size)))
        # note: hostile manipulation of the sequence' content (e.g., a
        # sequence storing itself in its payload) is not a problem here.
        # Further (virtual) memory corruption will be the result, but the
        # corruption cannot escape the VM
        var src = sp + 8

        if types[typ].kind == akSeq and vtfDataOnly notin types[elem].flags:
          # zero first so that destruction is disabled
          zeroMem(a.translate(target), slen * int64(types[elem].size))
          for _ in 0..<slen:
            recurse(target, src, elem)
            inc target, types[elem].size
            inc src,    types[elem].size
        else:
          copyMem(a.translate(target), a.translate(src), slen * int64(types[elem].size))

      # set the sequence fields:
      a.translate(dst).wr(int64, slen, 0)
      a.translate(dst).wr(VirtualAddr, p, 8)

  of akRef:
    let s = a.translate(src).rd(VirtualAddr)
    if s != nil:
      incRef(checked(a, s - 8, types[types[typ].elem].size))

    let d = a.translate(dst).rd(VirtualAddr)
    if d != nil:
      decRef(checked(a, d - 8, types[types[typ].elem].size), d - 8, a)

    copyMem(a.translate(dst), a.translate(src), sizeof(uint64))
  of akForeign:
    let
      d = a.translate(dst).rd(ForeignRef)
      s = a.translate(src).rd(ForeignRef)
    if s.isNonNil:
      check not(check(a, s))
      incRef(a, s)
    if d.isNonNil:
      check not(check(a, d))
      decRef(a, d)

    copyMem(a.translate(dst), a.translate(src), sizeof(ForeignRef))
  of akRecord:
    if vtfDataOnly in types[typ].flags:
      copyMem(a.translate(dst), a.translate(src), types[typ].size)
    else:
      for i, f in fields(types, typ):
        recurse(dst + f.off, src + f.off, f.typ)

  of akUnion:
    if vtfDataOnly in types[typ].flags:
      copyMem(a.translate(dst), a.translate(src), types[typ].size)
    else:
      let sel = types.fields[types[typ].a].typ
      let dtag = a.translate(dst).readUInt(types[sel].size)
      let stag = a.translate(src).readUInt(types[sel].size)
      if dtag != stag:
        # potentially a branch change, destroy and clear the destination
        # location first
        check destroy(a.translate(dst), types, typ, a)

      let branch = selectBranch(stag, types, typ)
      if branch >= 0:
        let off = types[sel].size
        copy(dst + off, src + off, types, types.branch(typ, branch), a)
      else:
        return true

  of akArray:
    if vtfDataOnly in types[typ].flags:
      copyMem(a.translate(dst), a.translate(src), types[typ].size)
    else:
      let
        (count, elem) = types.unpackArray(typ)
        stride = types[elem].size
      var
        dst = dst
        src = src
      for _ in 0..<count:
        recurse(dst, src, elem)
        inc dst, stride
        inc src, stride
  of akVoid, akFlexArray:
    unreachable()

#[
proc cleanup*(a: var VmAllocator, types: VmTypeEnv): bool =
  ## Destroys all stale ref-counted cells.
  while a.deferred.len > 0:
    let p = a.deferred.pop()
    let (host, typ) = mapPointerToCell(a, p)
    check host.isNil # not a valid ref or someone free the cell in-between
    check destroy(host + 8, types, typ, a)
    # TODO: the dealloc should be combined with mapping the virtual address to
    #       the cell
    check a.dealloc(p)
    # new cells were possibly added
]#

proc checkedCopy*(dst: VirtualAddr, src: VirtualAddr, types: VmTypeEnv, typ: VmTypeId, a: var VmAllocator): bool =
  ## Returns whether an out-of-bound access occurred.
  if unlikely(validate(a, dst, types[typ].size) or validate(a, src, types[typ].size)):
    true
  else:
    copy(dst, src, types, typ, a)

proc checkedDestroy*(dst: VirtualAddr, types: VmTypeEnv, typ: VmTypeId, a: var VmAllocator): bool =
  var d: HostPointer
  if unlikely(checkmem(a, dst, types[typ].size, d)):
    true
  else:
    destroy(d, types, typ, a)
