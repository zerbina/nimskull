
#
# This is an example implementation for a basic CPS-based iterator.
#

import std/options

# This is our iterator type. It holds the continuation function
# and an Option[int] to pass the last produced value

type Iterator = ref object of Coroutine
  val: Option[int]

# The `produce` proc is called to pump the iterator. It will trampoline the
# continuation until a value is available in `val`.

template trampolineIt[T](x: T, body: untyped) =
  while x.running:
    let it {.inject.} = resume(x)
    body
    x = T it

proc produce(c: sink Iterator): Option[int] =
  trampolineIt c:
    if (Iterator it).val.isSome:
      break
  if not c.dismissed:
    if c.val.isSome:
      result = c.val
      c.val = none(int)


# The `jield` proc is cps magic to generate a new value from within an
# interator

proc jield(c: Iterator, val: int): Iterator =
  c.val = some(val)
  return c


# A simple counting iterator, will produce all integers from 'lo' to 'high',
# inclusive

proc counter(lo, hi: int) {.coroutine:Iterator.} =
  var i = lo
  while i <= hi:
    cps jield(i)
    inc i


# Create an instance of the iterator, counting from 3 up to 7

var a = whelp counter(3, 7)

# Resume the iterator a bunch of times

echo "produced ", a.produce()
echo "produced ", a.produce()
echo "produced ", a.produce()
echo "produced ", a.produce()
echo "produced ", a.produce()
echo "produced ", a.produce()
