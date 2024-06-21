## Implements the allocator for the VM.

import compiler/vm/vmtypes
import compiler/utils/idioms
import std/options

type
  VirtualAddr* = distinct uint64
  ForeignRef* = distinct uint64

  HostPointer* = ptr UncheckedArray[byte]
    ## A pointer to some VM-owned memory, in the host's address space

  FreeProc = proc(p: pointer) {.nimcall, raises: [].}

  ChunkPtr = distinct uint32 # biased by 1, so that 0 means "nil"

  Chunk {.pure, inheritable.} = object
    ## Chunk for the heap allocator.
    start: uint # virtual offset
    size: uint32 # only 4GB per allocation
    prev: ChunkPtr
    next: ChunkPtr

  SmallChunk = object of Chunk
    free: uint8
    occupied: uint8
    types: UncheckedArray[VmTypeId]

  LargeChunk = object of Chunk
    typ: VmTypeId

  VmAllocator* = object
    ## The allocator state. The basic idea: there's only a single host
    ## allocation that backs all VM allocations. VM addresses use a virtual
    ## address space, which makes them independent from the host allocator and
    ## allows for relocating or growing the host allocation.

    # ------- host memory management
    host: HostPointer
      ## the host memory region that backs the virtual memory
    hostSize: uint
    maxHost*: uint
      ## maximum number of host memory the VM may occupy

    # ------- stack allocator
    stackCells: seq[tuple[typ: VmTypeId, start: uint32]]
    stackPointer: uint ## current top of the stack
    stackEnd: uint     ## maximum amount of usable stack memory

    # ------- heap allocator
    # The broad design: the memory region past the stack space is reserved for
    # the heap, it is subdivided into *chunks*. The memory region of each chunk
    # has the ID of the chunk written to it. Since chunks always start at a
    # fixed power-of-two boundary, this allows for O(1) checks whether a chunk
    # is allocated. For small allocations, normal chunks are subdivided
    chunks: seq[ptr Chunk]
      ## all chunks that exist.
    largeChunks: ChunkPtr
    freeSmall: array[1..8, ChunkPtr]
    freeLarge: ChunkPtr

    # ------- foreign cell management
    foreign: seq[tuple[p: pointer, rc: uint, free: FreeProc]]
      ## VM-foreign `ref` values. For empty cells, the `rc` values form an
      ## intrusive linked-list. `p` cannot be a ``RootRef``, since not foreign
      ## references aren't required to support polymorphism. As a consequence,
      ## the `free` value is required
      # XXX: we could also use a sequence per foreign reference type...
    nextForeign: uint
      ## the next free foreign cell
    zct*: seq[ForeignRef]
      ## zero-count table. Stores all slots that have (or had) an RC of 0

    deferred*: seq[VirtualAddr]

  StackInfo* = object
    cell: uint32  ## current top cell
    start: uint32 ## current stack pointer

const
  LargeChunkSize = 4096
    ## the minimum amount of bytes a single. Must be a power of 2
  ChunkMask = LargeChunkSize - 1
  ChunkOverhead = 4
    ## extra byte occupied per large chunk that cannot be used by allocations

proc `=copy`(a: var VmAllocator, b: VmAllocator) {.error.}

when not defined(debug):
  {.push checks: off.}

template isNil(x: ChunkPtr): bool = x.uint32 == 0
proc `==`(a, b: ChunkPtr): bool {.borrow.}

template `[]`(x: ChunkPtr): uint32 = x.uint32 - 1
template `[]`(x: seq[ptr Chunk], p: ChunkPtr): ptr Chunk = x[p[]]
template toPtr(x: uint32): ChunkPtr = ChunkPtr(x + 1)

proc initAllocator*(maxHost: uint): VmAllocator =
  result.maxHost = maxHost
  result.stackEnd = 1024 * 1024 # 2 megabyte
  # allocate the initial host memory:
  result.host = cast[HostPointer](alloc(result.stackEnd))
  result.hostSize = result.stackEnd

proc translate*(a: VmAllocator, p: VirtualAddr): HostPointer {.inline.} =
  ## Translate `p` to a host address. This is an *unsafe* operation, no checks
  ## are performed.
  cast[HostPointer](cast[uint64](a.host) + (uint64(p) - 8))

proc mapBack*(a: VmAllocator, p: pointer): VirtualAddr =
  # XXX: only meant for debugging
  VirtualAddr(cast[uint](p) - cast[uint](a.host) + 8)

proc safeChunk(a: VmAllocator, start: uint, id: var uint32): bool =
  let start = start and not(ChunkMask.uint)
  # note: the chunk ID as written in VM accessible memory is untrusted
  id = cast[ptr uint32](addr a.host[start])[]
  if id < a.chunks.len.uint32:
    # is the chunk ID sane?
    result = a.chunks[id].start == start
  else:
    result = false


proc safeCell(c: ptr SmallChunk, p: VirtualAddr, interior: bool, cell: var uint32): bool =
  let local = uint(p) - 8 - c.start
  cell = uint32(local div c.size)
  # picked the cell; is it actually allocated?

  if unlikely(not(interior) and (cell * c.size != local)):
    return false

  if unlikely(cell == 0 or local >= c.occupied * c.size):
    return false

  var i = c.free
  while i != 0:
    if unlikely(i == cell):
      return
    i = cast[uint8](c.types[i - 1])

  dec cell
  result = true

proc mapPointerToCell*(a: VmAllocator, p: VirtualAddr): tuple[p: HostPointer, typ: VmTypeId] =
  ## Only meant for heap cells.
  var id: uint32
  if unlikely(not safeChunk(a, uint(p) - 8, id)):
    return # not allocated, or the heap is corrupt

  if a.chunks[id].size < LargeChunkSize:
    # small chunk
    let cell = ((uint(p) - 8) and ChunkMask) div a.chunks[id].size
    result.p = cast[HostPointer](cast[uint](a.host) + a.chunks[cell].start)
    result.typ = cast[ptr SmallChunk](a.chunks[id]).types[cell - 1]
  else:
    result.p = cast[HostPointer](cast[uint](a.host) + a.chunks[id].start)
    result.typ = cast[ptr LargeChunk](a.chunks[id]).typ

proc allocStack*(a: var VmAllocator, size, align: uint, typ: VmTypeId): (VirtualAddr, uint32) =
  ## Alocates memmory from the program *stack*. In the context of the VM, this
  ## is typed memory that can only grow and shrink like a stack. Therefore,
  ## it's much faster to allocate and deallocate from, compared to the heap.
  assert align > 0
  let start = (a.stackPointer + (align-1)) and not(align-1)
  if likely(start + size <= a.stackEnd):
    result = (VirtualAddr(start + 8), a.stackCells.len.uint32)
    a.stackCells.add (typ, start.uint32)
    a.stackPointer = start + size
  else:
    result = (VirtualAddr(0), 0'u32) # stack overflow

proc save*(a: VmAllocator): StackInfo {.inline.} =
  StackInfo(start: a.stackPointer.uint32, cell: a.stackCells.len.uint32)

proc restore*(a: var VmAllocator, to: StackInfo) {.inline.} =
  a.stackPointer = to.start.uint
  a.stackCells.setLen(to.cell)

proc stack*(a: VmAllocator, i: uint32): (VmTypeId, HostPointer) {.inline.} =
  result = (a.stackCells[i].typ, cast[HostPointer](cast[uint](a.host) + a.stackCells[i].start))

proc integrity(a: VmAllocator, id: ChunkPtr) =
  if not a.chunks[id].prev.isNil:
    doAssert a.chunks[a.chunks[id].prev].next == id
  if not a.chunks[id].next.isNil:
    doAssert a.chunks[a.chunks[id].next].prev == id, repr(id) & "; " & repr(a.chunks)

proc integrity(a: VmAllocator): bool =
  defer:
    if result:
      debugEcho repr(a.chunks)

  var f = a.largeChunks
  var s: seq[ChunkPtr]
  while not f.isNil:
    doAssert f notin s, repr(s) & " -- " & $f.int
    integrity(a, f)
    s.add f
    f = a.chunks[f].next

  f = a.freeLarge
  reset(s)
  while not f.isNil:
    doAssert f notin s, repr(s) & " -- " & $f.int
    s.add f
    f = a.chunks[f].next

  for i, it in a.chunks.pairs:
    if it.size < LargeChunkSize and cast[ptr uint32](addr a.host[it.start])[] != uint32(i):
      debugEcho "wrong: ", cast[ptr uint32](addr a.host[it.start])[], " for: ", i, ", ", it[]
      return true
    if it.size < LargeChunkSize:
      let c = cast[ptr SmallChunk](it)
      var f = c.free
      var s: seq[uint8]
      while f != 0:
        doAssert f notin s, $s & " -- " & $f.int
        s.add(f)
        f = cast[uint8](c.types[f - 1])

      var j = a.freeLarge
      while not j.isNil:
        doAssert j != toPtr(i.uint32)
        j = a.chunks[j].next
      doAssert c.occupied != 0, repr(a.chunks)

proc isFull(a: SmallChunk): bool =
  a.free == 0 and (uint16(a.occupied) + 1) * a.size >= LargeChunkSize

proc allocChunk(a: var VmAllocator, size: uint32, control: int): ChunkPtr =
  # chunks have a size that's a multiple of ``LargeChunkSize``
  let realSize = (size + 8 + ChunkMask) and not(ChunkMask.uint32)

  var i = a.freeLarge
  var prev = ChunkPtr(0)
  # first fit
  while not i.isNil and a.chunks[i].size < size:
    prev = i
    i = a.chunks[i].next

  if unlikely(i.isNil):
    # slow path: grow the VM memory
    let newSize = max(a.hostSize * 2, a.hostSize + realSize)
    if unlikely(newSize > a.maxHost):
      return # out of memory

    debugEcho "--- resize: ", newSize

    a.host = cast[HostPointer](realloc(a.host, newSize))

    # add a chunk covering the whole new free heap memory
    a.chunks.add create(LargeChunk)
    a.chunks[^1][] = Chunk(start: a.hostSize, size: uint32(newSize - a.hostSize))
    a.hostSize = newSize
    i = a.chunks.len.ChunkPtr
  else:
    if i == a.freeLarge:
      a.freeLarge = a.chunks[i].next
    else:
      a.chunks[prev].next = a.chunks[i].next

  result = i
  let r = i[]
  if a.chunks[r].size == realSize:
    # fits exactly
    if control != sizeof(LargeChunk):
      let n = cast[ptr Chunk](alloc0(control))
      n.size = a.chunks[r].size
      n.start = a.chunks[r].start
      dealloc(a.chunks[r])
      a.chunks[r] = n
  else:
    # split the chunk
    a.chunks[r].next = a.freeLarge
    a.chunks[r].prev = ChunkPtr(0)
    a.freeLarge = result

    let n = cast[ptr Chunk](alloc0(control))
    n.start = a.chunks[r].start
    n.size = realSize
    a.chunks[r].start += realSize
    a.chunks[r].size -= realSize
    a.chunks.add n
    result = a.chunks.len.ChunkPtr

  a.chunks[result].next = ChunkPtr(0)
  assert (a.chunks[result].start and ChunkMask) == 0

  # write the chunk ID to the start of its region
  cast[ptr uint32](addr a.host[a.chunks[result].start])[] = result[]

proc alloc*(a: var VmAllocator, size: uint; typ = VoidType): VirtualAddr =
  ## Allocates a memory region of `size` with no type.
  assert size > 0
  let num = ((size + 15) div 16)

  var start = 0'u
  if num.int - 1 < a.freeSmall.len:
    let cs = num * 16
    let i = a.freeSmall[num]

    var c: ptr SmallChunk
    var p = 0'u16
    if likely(not i.isNil):
      c = cast[ptr SmallChunk](a.chunks[i])
      if c.free != 0:
        p = c.free
        c.free = cast[uint8](c.types[p - 1])
      else:
        p = c.occupied
        inc c.occupied

      if isFull(c[]):
        # remove from free list
        a.freeSmall[num] = c.next

      if cast[ptr uint32](addr a.host[c.start])[] != i[]:
        debugEcho "wrong: ", cast[ptr uint32](addr a.host[c.start])[]
        return VirtualAddr(0)
    else:
      let id = allocChunk(a, LargeChunkSize - 8, sizeof(SmallChunk) + sizeof(VmTypeId) * ((LargeChunkSize /% int(cs)) - 1))
      if unlikely(id.isNil):
        return # out of memory

      c = cast[ptr SmallChunk](a.chunks[id])
      # small chunks use their cell size as their chunk size
      c.size = uint32(cs)
      c.occupied = 2
      p = 1

      # the chunk has some free cells
      c.next = a.freeSmall[num]
      a.freeSmall[num] = id

    start = c.start + (p * cs)
    c.types[p - 1] = typ

  else:
    # TODO: size overflow checks
    let id = allocChunk(a, size.uint32, sizeof(LargeChunk))
    if unlikely(id.isNil):
      return

    let c = cast[ptr LargeChunk](a.chunks[id])
    # add to the list
    c.prev = ChunkPtr(0)
    c.next = a.largeChunks
    if not a.largeChunks.isNil:
      a.chunks[a.largeChunks].prev = id

    a.largeChunks = id
    c.typ = typ
    start = c.start + 8

  result = VirtualAddr(start + 8)

proc alloc0*(a: var VmAllocator, size: uint; typ = VoidType): VirtualAddr {.inline.} =
  result = alloc(a, size, typ)
  if likely(result.uint64 != 0):
    zeroMem(a.translate(result), size)

proc freeChunk(a: var VmAllocator, id: uint32) =
  let p = toPtr id
  if a.largeChunks == p:
    a.largeChunks = a.chunks[a.largeChunks].next
    if not(a.largeChunks.isNil):
      a.chunks[a.largeChunks].prev = ChunkPtr(0)
  else:
    a.chunks[a.chunks[id].prev].next = a.chunks[id].next
    if not a.chunks[id].next.isNil:
      a.chunks[a.chunks[id].next].prev = a.chunks[id].prev

  a.chunks[id].next = a.freeLarge
  a.chunks[id].prev = ChunkPtr(0)
  if not a.freeLarge.isNil:
    a.chunks[a.freeLarge].prev = p
  a.freeLarge = p

proc freeSmall(a: var VmAllocator, id: uint32, cell: int) =
  let c = cast[ptr SmallChunk](a.chunks[id])
  if isFull(c[]):
    # add to the free list
    c.next = a.freeSmall[c.size div 16]
    c.prev = ChunkPtr(0)
    a.freeSmall[c.size div 16] = toPtr id

  if uint16(cell + 2) * uint16(c.size) == c.occupied * c.size:
    dec c.occupied
  else:
    c.types[cell] = cast[VmTypeId](c.free)
    c.free = uint8(cell + 1)

  # XXX: free the whole chunk if it becomes fully empty?

proc realloc*(a: var VmAllocator, p: VirtualAddr, size: uint): VirtualAddr =
  if p.int == 0:
    return alloc(a, size)

  var id: uint32
  if unlikely(not safeChunk(a, uint(p) - 8, id)):
    return

  if a.chunks[id].size < LargeChunkSize:
    var cell: uint32
    if unlikely(not safeCell(cast[ptr SmallChunk](a.chunks[id]), p, false, cell)):
      return

    if a.chunks[id].size >= size:
      result = p # still fits
    else:
      result = alloc(a, size, cast[ptr SmallChunk](a.chunks[id]).types[cell])
      if unlikely(result.uint64 == 0):
        return # out of memory
      copyMem(a.translate(result), a.translate(p), a.chunks[id].size)
      freeSmall(a, id, cell.int)
  elif size <= LargeChunkSize - ChunkOverhead:
    # just keep the chunk as is
    # TODO: if getting small enough, the cell should be relocated
    result = p
  else:
    # TODO: try to merge with the neighbour chunk
    result = alloc(a, size, cast[ptr LargeChunk](a.chunks[id]).typ)
    if unlikely(result.uint64 == 0):
      return # out of memory
    copyMem(a.translate(result), a.translate(p), a.chunks[id].size)
    freeChunk(a, id)

proc dealloc*(a: var VmAllocator, p: VirtualAddr): bool =
  var id: uint32
  if unlikely(not safeChunk(a, uint(p) - 8, id)):
    return true # not allocated or some interior pointer

  if a.chunks[id].size < LargeChunkSize:
    var cell: uint32
    if unlikely(not safeCell(cast[ptr SmallChunk](a.chunks[id]), p, false, cell)):
      return true # not allocated

    freeSmall(a, id, cell.int)
  else:
    freeChunk(a, id)

proc checkmem*(a: VmAllocator, address: VirtualAddr, len: uint64,
               o: var HostPointer): bool {.inline.} =
  ## * if `a` points to `len` bytes all owned by the VM, writes the host
  ##   address to `o` and returns false
  ## * otherwise leaves `o` unchanged an returns true
  let x = uint64(address)
  if likely(x >= 8 and x + len <= a.hostSize + 8):
    o = cast[HostPointer](cast[uint](a.host) + (x - 8))
    false
  else:
    true # error

proc mapInteriorPointerToCell*(a: VmAllocator, p: VirtualAddr): tuple[p: HostPointer, base: VirtualAddr, size: uint, offset: uint, typ: VmTypeId] =
  ## Maps interior pointer `p` to the cell it's part of, or none, if it's not
  ## allocated.
  if unlikely(p.uint < 8):
    return
  let p = uint64(p) - 8

  if p < a.stackEnd:
    # it's stack memory
    # TODO: use a binary search, or something else that's faster than a
    #       linear search
    var i = 0
    while i < a.stackCells.len:
      if a.stackCells[i].start > p:
        break
      inc i

    if likely(i > 0):
      let it = a.stackCells[i - 1]
      result = (a.translate(VirtualAddr(p+8)), VirtualAddr(it.start + 8), 0'u, uint(p - it.start.uint), it.typ)
    else:
      return # no cell found
  else:
    # quick check
    var id: uint32
    if safeChunk(a, p.uint, id) and a.chunks[id].size < LargeChunkSize:
      let c = cast[ptr SmallChunk](a.chunks[id])
      var cell: uint32
      if unlikely(not safeCell(c, VirtualAddr(p + 8), true, cell)):
        return # not allocated

      let base = c.start + (cell + 1) * c.size
      result = (a.translate(VirtualAddr(p+8)), VirtualAddr(base + 8), c.size.uint, uint(p - base), c.types[cell])
    else:
      # slow path: look through the list of large chunks
      var i = a.largeChunks
      while not i.isNil:
        let c = cast[ptr LargeChunk](a.chunks[i])
        if c.start + 8 <= p and c.start + c.size > p:
          break
        i = c.next

      if unlikely(i.isNil):
        return # not allocated

      let c = cast[ptr LargeChunk](a.chunks[i])
      result = (a.translate(VirtualAddr(p+8)), VirtualAddr(c.start + 8 + 8), c.size.uint, uint(p - (c.start + 8)), c.typ)

proc destroy[T: ref](x: pointer) =
  GC_unref cast[T](x)

proc register*[T: ref](a: var VmAllocator, r: T): ForeignRef =
  ## Register the foreign reference `r` with the allocator.
  # TODO: don't add duplicates? Could use a pointer set, but maybe
  #       that's not worth the overhead?
  if r.isNil:
    return ForeignRef(0)

  GC_ref(r)
  result = (a.nextForeign + 1).ForeignRef
  if a.nextForeign < a.foreign.len.uint:
    let next = a.foreign[a.nextForeign].rc
    a.foreign[a.nextForeign] = (cast[pointer](r), 1'u shl 63, destroy[T])
    a.nextForeign = next
  else:
    a.foreign.add (cast[pointer](r), 1'u shl 63, destroy[T])
    inc a.nextForeign

  # every new foreign ref starts off in the ZCT
  a.zct.add result

template isNonNil*(r: ForeignRef): bool =
  r.uint64 != 0

template incRef*(a: var VmAllocator, r: ForeignRef) =
  inc a.foreign[r.uint64 - 1].rc

template decRef*(a: var VmAllocator, r: ForeignRef) =
  let s = r.uint64 - 1
  dec a.foreign[s].rc
  if a.foreign[s].rc == 0:
    a.foreign[s].rc = 1'u shl 63 # mark as being in the ZCT
    a.zct.add ForeignRef(s+1)

proc free*(a: var VmAllocator, r: ForeignRef) =
  ## Releases the foreign reference `r`.
  let idx = r.uint64 - 1
  a.foreign[idx].free(a.foreign[idx].p)
  a.foreign[idx].p = nil
  a.foreign[idx].rc = a.nextForeign.uint
  a.nextForeign = idx.uint

proc cleanup*(a: var VmAllocator, r: ForeignRef) =
  let i = r.uint64 - 1
  if a.foreign[i].rc == 1'u shl 63:
    free(a, r)
  else:
    # non-zero refcount -> remove the ZCT flag
    a.foreign[i].rc = a.foreign[i].rc and not(1'u shl 63)

template lookup*[T](a: VmAllocator, id: ForeignRef, _: typedesc[T]): T =
  # a template, to get around the lent or copy
  cast[T](a.foreign[id.int - 1].p)

template check*(a: VmAllocator, id: ForeignRef): bool =
  (id.int in 1..a.foreign.len) and a.foreign[id.int-1].p != nil # the ID is biased by 1

proc show*(a: VmAllocator) =
  echo "small: ", repr(a.freeSmall)
  echo "chunkS: ", a.chunks.len
  echo "large: ", repr(a.freeLarge)

  echo "stack: ", a.stackCells.len
  echo "sp: ", a.stackPointer
