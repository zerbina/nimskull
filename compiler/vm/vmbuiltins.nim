## Bytecode implementations of various procedures needed by the code generator.

# import compiler/vm/vmgen
import compiler/ast/ast_types
import compiler/utils/bitsets
import compiler/vm/[vmdef, vmalloc, vmobjects, vmtypes, vmconv]

template callback(name, body: untyped): untyped {.dirty.} =
  yield (name, proc (env: var VmEnv, args: openArray[StackValue], cl: RootRef): (CallbackExitCode, StackValue) =
    body
  )

template error() =
  return (cecError, StackValue(0))

iterator builtins*(): (string, VmCallback) =
  callback "__builtin_strSetLen":
    # echo "__builtin_strSetLen"
    if args.len == 1:
      error()
    let len = cast[BiggestInt](args[1])
    # echo "setlen: ", len
    var dst: HostPointer
    if checkmem(env.allocator, cast[VirtualAddr](args[0]), 8, dst):
      error()

    let p = dst.rd(VirtualAddr, 8)
    var cap = 0'i64
    if p != 0:
      var payload: HostPointer
      if checkmem(env.allocator, p, 8, payload):
        error()

      cap = payload.load(int64)

    # echo "cap: ", cap
    if cap < len:
      let n = env.allocator.realloc(p, len.uint + 8)
      if n == 0: error()
      env.allocator.translate(n).store(int64(len))
      dst = env.allocator.translate(cast[VirtualAddr](args[0])) # remap
      dst.wr(VirtualAddr, n, 8)
    dst.store(int64(len))
  callback "__builtin_appendStrChar":
    # echo "__builtin_appendStrChar"
    var dst: HostPointer
    if checkmem(env.allocator, cast[VirtualAddr](args[0]), 16, dst):
      return

    let orig = dst.load(int64)
    let len = orig + 1
    let p = dst.rd(VirtualAddr, 8)
    var cap = 0'i64
    var payload: HostPointer
    if p != 0:
      if checkmem(env.allocator, p, 8, payload):
        error()

      cap = payload.load(int64)

    if cap < len:
      let n = env.allocator.realloc(p, len.uint + 8)
      if n == 0: error()
      env.allocator.translate(n).store(int64(len))
      payload = env.allocator.translate(n)
      dst = env.allocator.translate(cast[VirtualAddr](args[0])) # remap
      dst.wr(VirtualAddr, n, 8)
    payload.wr(char, cast[char](args[1]), int(orig+8))
    dst.store(int64(len))
  callback "__builtin_appendStrStr":
    # echo "__builtin_appendStrStr"
    var dst: HostPointer
    if checkmem(env.allocator, cast[VirtualAddr](args[0]), 16, dst):
      error()

    var src: HostPointer
    if checkmem(env.allocator, cast[VirtualAddr](args[1]), 16, src):
      error()

    let srclen = src.load(int64)
    let len = dst.load(int64)
    if srclen <= 0:
      return # nothing to do

    let newlen = len + srclen
    let p = dst.rd(VirtualAddr, 8)
    var payload: HostPointer
    var cap = 0'i64
    if p != 0:
      if checkmem(env.allocator, p, 8, payload):
        error()
      cap = payload.load(int64)

    var spayload: HostPointer
    let sp = src.rd(VirtualAddr, 8)
    if checkmem(env.allocator, sp + 8, uint srclen, spayload):
      error()

    if cap < newlen:
      let n = env.allocator.realloc(p, newlen.uint + 8)
      if n == 0: error()
      env.allocator.translate(n).store(int64(newlen))
      dst = env.allocator.translate(cast[VirtualAddr](args[0])) # remap
      payload = env.allocator.translate(n)
      spayload = env.allocator.translate(sp + 8)
      dst.wr(VirtualAddr, n, 8)

    copyMem(addr payload[len + 8], addr spayload[0], uint32 srclen)
    dst.wr(int64, newlen)
  callback "__prepareSeqAdd":
    let typ = VmTypeId args[1]
    var dst: HostPointer
    if checkmem(env.allocator, cast[VirtualAddr](args[0]), 16, dst):
      return

    let orig = dst.load(int64)
    let len = orig + 1
    let p = dst.rd(VirtualAddr, 8)
    var cap = 0'i64
    var payload: HostPointer
    if p != 0:
      if checkmem(env.allocator, p, 8, payload):
        error()

      cap = payload.load(int64)

    if cap < len:
      cap = max(cap * 2, len.int64)
      let n = env.allocator.realloc(p, uint(cap) * env.types[typ].size + 8)
      if n == 0: error()
      env.allocator.translate(n).store(int64(cap))
      dst = env.allocator.translate(cast[VirtualAddr](args[0])) # remap
      dst.wr(VirtualAddr, n, 8)

    let elem = 8 + (uint(orig) * env.types[typ].size)
    if vtfDataOnly notin env.types[typ].flags:
      # TODO: only needed for foreign references. Support moves for WrRef and
      #       remove this special case
      if checkmem(env.allocator, dst.rd(VirtualAddr, 8) + elem, env.types[typ].size, payload):
        error()
      zeroMem(payload, env.types[typ].size)

    dst.store(int64(len))
    result = (cecValue, StackValue (dst.rd(VirtualAddr, 8) + elem))
  callback "__card":
    var src: HostPointer
    if checkmem(env.allocator, cast[VirtualAddr](args[0]), args[1].BiggestUInt, src):
      error()

    result[0] = cecValue
    result[1] = StackValue bitSetCard(src.toOpenArray(0, args[1].int-1))
  callback "__builtin_eqStr":
    var a: HostPointer
    if checkmem(env.allocator, cast[VirtualAddr](args[0]), 16, a):
      error()
    var b: HostPointer
    if checkmem(env.allocator, cast[VirtualAddr](args[1]), 16, b):
      error()

    let len = a.load(int64)
    if len != b.load(int64):
      return (cecValue, StackValue 0)

    var memA, memB: HostPointer
    if checkmem(env.allocator, a.rd(VirtualAddr, 8) + 8, uint len, memA) or
       checkmem(env.allocator, b.rd(VirtualAddr, 8) + 8, uint len, memB):
      error()

    result[0] = cecValue
    result[1] = StackValue ord(cmpMem(memA, memB, len) == 0)
  callback "__charToStr":
    let str = $char(cast[uint64](args[1]))
    # TODO: format directly into the destination string
    if not writeString(env, VirtualAddr(args[0]), str):
      error()
  callback "__newseq":
    let typ = cast[VmTypeId](args[2])

    var dst: HostPointer
    let len = args[1].int64
    if checkmem(env.allocator, cast[VirtualAddr](args[0]), 16, dst):
      error()

    var a = newSeqPayload(env.allocator, len, env.types[env.types[typ].elem].size)
    dst = env.allocator.translate(cast[VirtualAddr](args[0])) # remap
    dst.wr(int64, len)
    dst.wr(VirtualAddr, a, 8)
    if len > 0:
      zeroMem(env.allocator.translate(a + 8), len * int64 env.types[env.types[typ].elem].size)
  callback "__newstr":
    var dst: HostPointer
    let len = args[1].int64
    if checkmem(env.allocator, cast[VirtualAddr](args[0]), 16, dst):
      error()

    var a = newSeqPayload(env.allocator, len, 1)
    dst = env.allocator.translate(cast[VirtualAddr](args[0])) # remap
    dst.wr(int64, len)
    dst.wr(VirtualAddr, a, 8)
    if len > 0:
      zeroMem(env.allocator.translate(a + 8), len)
  callback "__newobj":
    let typ = cast[VmTypeId](args[0])
    let size = env.types[typ].size
    let res = env.allocator.alloc0(size, typ)
    if res.uint64 == 0:
      error()
    result = (cecValue, cast[StackValue](res + 8)) # +8 for the refcounter field
