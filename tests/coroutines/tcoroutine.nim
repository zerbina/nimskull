discard """
"""

# Import cps and short `=>` syntax for anonymous functions
import std/sugar

type
  Coro = ref object of Coroutine
    data: int
    suspended: Coro

# Used to both launch and continue the execution of coroutines
template resume(c: Coro): untyped =
  discard trampoline c

proc recv(c: Coro): int =
  c.data

# Suspend execution of the coroutine
proc suspend(c: Coro): Coro =
  c.suspended = c

proc send(c: Coro, n: int) =
  c.data = n
  resume c.suspended

# This coroutine receives the data, applies f and sends the result to consumer
proc filter(dest: Coro, f: proc(x: int): int) {.coroutine: Coro.} =
  while true:
    cps suspend()
    let n = f(recv(self))
    dest.send(n)

# This coroutine receives ints through filter and prints them
proc consumer() {.coroutine:Coro.} =
  while true:
    cps suspend()
    let value = recv(self)
    echo value

let coro2 = whelp consumer()
let coro1 = whelp filter(coro2, x => x * 2)

resume coro1
resume coro2

# This prints numbers from 2 to 20 in 2 increment.
for i in 1..10:
  coro1.send(i)

# break the cycles
reset coro1.suspended
reset coro2.suspended
