import std/deques
import std/macros
import std/sugar

###########################################################################
# Lazy streams
###########################################################################

type
  Stream = ref object of Coroutine  ## a stream chains transformations...
    val: int                        ## ...of integers.
    next2: Stream

{.pragma: stream, coroutine: Stream.}

proc jield(s: Stream; val: int = 0): Stream =
  ## emit a value into the stream
  s.val = val

proc next(s: Stream): var Stream =
  ## the next stream in the chain
  s.next2

proc run(s: var Stream): int {.discardable.} =
  ## run a stream to produce a value
  discard trampoline s
  result = s.val

template `->`(ca: Stream, b: typed): Stream =
  ## composition operator
  let cb = whelp(b)
  cb.next2 = ca
  cb

template `->`(a, b: typed): Stream =
  ## composition operator
  let ca = whelp(a)
  let cb = whelp(b)
  cb.next2 = ca
  cb


###########################################################################

proc toStream(slice: Slice[int]) {.stream.} =
  ## turn any slice into a lazy stream
  var i = slice.a
  while i <= slice.b:
    cps jield i
    inc i

proc map(fn: proc(x: int): int) {.stream.} =
  ## lazily apply a function to a stream
  while true:
    let v = fn: run next(self)
    if next(self).finished: break
    cps jield(v)

proc filter(fn: proc(x: int): bool) {.stream.} =
  ## lazily apply a predicate to a stream
  while true:
    let v = run next(self)
    if next(self).finished: break
    if fn(v):
      cps jield(v)

proc print() {.stream.} =
  ## lazily echo a stream
  while true:
    let v = run next(self)
    if next(self).finished: break
    echo v
    cps jield()

proc pump() {.stream.} =
  ## iterate the stream processor
  while next(self).running:
    run next(self)


when isMainModule:
  # create a lazy stream
  var s =
    toStream(1..50) ->
    map(x => x * 3) ->
    filter(x => (x mod 2) == 0) ->
    print() ->
    pump()

  # lazily run it
  run s
