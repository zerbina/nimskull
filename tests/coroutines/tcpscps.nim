discard """
"""

import deques

###########################################################################
# Implementation of a minimal scheduler, just a dequeue of work
###########################################################################

type
  Work = ref object of Coroutine
    pool: Pool

  Pool = ref object
    workQueue: Deque[Work]
    yields: int

proc push(pool: Pool, c: Work) =
  if c.running:
    echo "pool was supplied to push"
    c.pool = pool
    pool.workQueue.addLast(c)

proc jield(c: Work): Work =
  inc c.pool.yields
  c.pool.push c

proc run(pool: Pool) =
  while pool.workQueue.len > 0:
    var c = Coroutine: pool.workQueue.popFirst
    echo "trampo"
    c = trampoline c
    pool.push c.Work

proc tail(mom: Coroutine; c: Work): Work =
  echo "tail copied the pool"
  result = c
  result.next = mom
  result.pool = mom.Work.pool

###########################################################################
# Main code
###########################################################################

var total: int

proc deeper(b: ref int) {.coroutine:Work.} =
  echo "  deeper() in, b: ", b[]
  cps jield()
  inc total, b[]
  echo "  deeper() out"

proc foo(a: int) {.coroutine:Work.} =
  echo " foo() in a: ", a
  echo " foo() yield()"
  cps jield()
  echo " foo() yield done()"
  echo " foo() calls deeper()"
  # CPS does not support var parameters yet. We can box an int tho
  var b = new int;
  b[] = a * 2
  cps tail(whelp deeper(b))
  echo " foo() returned from deeper(), b: ", b[]
  echo " foo() out"

proc bar() {.coroutine:Work.} =
  echo "bar() in"
  echo "bar() yield"
  cps jield()
  echo "bar() yield done"
  echo "bar() calls foo(1)"
  cps tail(whelp foo(1))
  echo "bar() returned from foo()"
  echo "bar() calls foo(2)"
  cps tail(whelp foo(2))
  echo "bar() returned from foo()"
  echo "bar() out"


var pool = Pool()
pool.push: Work whelp bar()
pool.run()

echo pool.yields
doAssert pool.yields == 5
echo total
doAssert total == 6
