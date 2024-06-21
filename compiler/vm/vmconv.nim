## Implements convenience routines for writing or reading |NimSkull| values to
## or from VM locations.

import
  compiler/front/[
    options
  ],
  compiler/utils/[
    bitsets, idioms
  ],
  compiler/vm/[
    vmdef,
    vmerrors,
    vmalloc,
    vmobjects,
    # vmmemory
  ]

proc readString*(env: VmEnv, p: VirtualAddr, to: var string): bool =
  var str: HostPointer
  if checkmem(env.allocator, p, 16, str):
    return
  let len = str.rd(int64, 0)
  to.setLen(len)
  if len == 0:
    return true

  var content: HostPointer
  if checkmem(env.allocator, str.rd(VirtualAddr, 8) + 8, uint(len), content):
    return

  copyMem(addr to[0], content, to.len)
  result = true

proc writeString*(env: var VmEnv, dst: VirtualAddr, src: string): bool =
  var str: HostPointer
  if checkmem(env.allocator, dst, 16, str):
    return false

  # set the length:
  # XXX: duplicated from vmbuiltins. Move the code to some shared location
  var p = str.rd(VirtualAddr, 8)
  var cap = 0'i64
  if p != 0:
    var payload: HostPointer
    if checkmem(env.allocator, p, 8, payload):
      return false
    cap = payload.load(int64)

  if cap < src.len:
    p = env.allocator.realloc(p, src.len.uint + 8)
    if p == 0: return false
    env.allocator.translate(p).store(int64(src.len))
    str = env.allocator.translate(dst) # remap
    str.wr(VirtualAddr, p, 8)

  str.wr(int64, int64(src.len), 0)
  # copy the content:
  if src.len > 0:
    copyMem(env.allocator.translate(p + 8), addr src[0], src.len)
  return true

proc readString*(env: var VmEnv, p: VirtualAddr): string =
  # TODO: unsafe. Remove
  if not readString(env, p, result):
    echo "error"

proc writeTo*[T: string](env: var VmEnv, val: T, to: VirtualAddr): bool =
  writeString(env, to, val)

proc writeTo*[T: object|tuple](env: var VmEnv, val: T, to: VirtualAddr): bool =
  for f in fields(val):
    if not writeTo(env, f, to + offsetof(f)):
      return false
  result = true

proc writeTo*[T: seq](env: var VmEnv, val: T, to: VirtualAddr): bool =
  # TODO: we need access to the proc signature in the callback somehow...
  missing("seq writing")

#[
proc tryWriteTo*[T: enum](v: T, dest: LocHandle, mm: var VmMemoryManager): bool =
  if dest.typ.kind == akInt:
    result = true
    # XXX: this will silently cut off bits beyond what dest can hold
    writeUInt(dest.byteView(), ord(v))


proc tryWriteTo*[T: SomeSignedInt](v: T, dest: LocHandle, mm: var VmMemoryManager): bool =
  if dest.typ.kind == akInt:
    result = true
    # XXX: this will silently cut off bits beyond what dest can hold
    writeInt(dest.byteView(), BiggestInt(v))


proc tryWriteTo*[T: SomeUnsignedInt](v: T, dest: LocHandle, mm: var VmMemoryManager): bool =
  if dest.typ.kind == akInt:
    result = true
    # XXX: this will silently cut off bits beyond what dest can hold
    writeUInt(dest, BiggestUInt(v))

proc tryWriteTo*[T: string](v: T, dest: LocHandle, mm: var VmMemoryManager): bool =
  if dest.typ.kind == akString:
    result = true
    deref(dest).strVal.newVmString(v, mm.allocator)
  else:
    result = false

proc tryWriteTo*[T: seq](v: T, dest: LocHandle, mm: var VmMemoryManager): bool =
  if dest.typ.kind == akSeq:
    deref(dest).seqVal.setLenSeq(dest.typ, v.len, mm)

    let s = deref(dest).seqVal # shallow copy
    for i in 0..<v.len:
      if tryWriteTo(v[i], s.getItemHandle(dest.typ, i, mm.allocator), mm): discard
      else: return false

    result = true

proc tryWriteTo*[T: object|tuple](v: T, dest: LocHandle, mm: var VmMemoryManager): bool =
  var fI = 0
  # XXX: this might be bit fuzzy for more complex objects...
  for x in v.fields:
    if tryWriteTo(x, dest.getFieldHandle(FieldPosition(fI)), mm): discard
    else: return false
    inc fI

  result = true

proc writeTo*[T](v: T, dest: LocHandle, mm: var VmMemoryManager) =
  if tryWriteTo(v, dest, mm):
    return

  raiseVmError(VmEvent(
    kind: vmEvtErrInternal,
    msg: "Writing to location failed: " & $T))


func tryReadTo*[T](src: LocHandle, dst: var set[T]): bool =
  const ElemRange = low(T)..high(T)
  if src.typ.kind == akSet and src.typ.setLength <= len(ElemRange):
    # TODO: do something more efficient than testing for each possible element
    for i in ElemRange:
      if bitSetIn(src.byteView(), ord(i)):
        dst.incl i
    result = true

func readAs*[T](src: LocHandle, t: typedesc[T]): T =
  if tryReadTo(src, result):
    return

  raiseVmError(VmEvent(
    kind: vmEvtErrInternal,
    msg: "Reading from location failed"))

]#