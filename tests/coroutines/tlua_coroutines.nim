
###########################################################################
#
# Lua-style assymetrical coroutines
#
# resume(co, val):
#
#   Starts or continues the execution of coroutine co. The first time you
#   resume a coroutine, it starts running its body. If the coroutine has
#   yielded, resume() restarts it; the value `val` is passed as the results
#   from the yield().
#
#  send(val):
#  yield():
#
#   Suspends the execution of the calling coroutine. The value `val`
#   passed to sent is returned as results from resume().
#
###########################################################################

import options, deques

type
  LuaCoro = ref object of Coroutine
    val: int

# Magic procs for yielding and receiving. Note: we actually want
# to have yield() and receive() in one single operation so we can
# do `vlaOut = yield(valIn)`

proc jield(c: LuaCoro, val: int): LuaCoro =
  c.val = val

proc recv(c: LuaCoro): int =
  return c.val

proc resume(c: LuaCoro, val: int): int =
  c.val = val
  discard c.trampoline()
  return c.val

# This coroutine calculates the running total of the passed numbers

proc fn_coro1() {.coroutine:LuaCoro.} =
  var sum = 0
  while true:
    sum += recv(self)
    cps jield(sum)

var coro = whelp fn_coro1()

for i in 0..10:
  echo coro.resume(i)
