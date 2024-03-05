discard """
  matrix: "--gc:arc --threads:on --threadanalysis:off"
  knownIssue.js vm: "No thread support"
"""

#
# Simple test of a naive threadpool for scheduling CPS threads. This demo
# creates many 'threads' scheduled on all available CPUs in the system
#
# nim r --gc:arc --threads:on --threadanalysis:off stash/threadpool.nim
#

import math, std/locks, deques, cpuinfo

###########################################################################
# Implementation of the thread pool
###########################################################################

type Cont = ref object of Coroutine


type Pool = ref object
  work: Deque[Cont]
  lock: Lock

proc newPool(): Pool =
  result = Pool()
  initLock(result.lock)


var pool = newPool()

proc doWork(pool: Pool) {.thread.} =

  while true:

    pool.lock.acquire
    if pool.work.len == 0:
      pool.lock.release
      return

    var c = Coroutine: pool.work.popFirst
    pool.lock.release

    if c.dismissed:
      break
    else:
      c = trampoline c


proc work(nThreads: int) =
  var threads: seq[Thread[Pool]]
  newSeq(threads, nThreads)
  for i in 0..<nThreads:
    createThread(threads[i], doWork, pool)
  joinThreads(threads)


proc jield(c: Cont): Cont =
  if c != nil:
    pool.lock.acquire
    pool.work.addLast(c)
    pool.lock.release

###########################################################################
# Main code
###########################################################################

var L: Lock
initLock L

proc slow(id: int, n: float) {.coroutine:Cont.} =
  var i, j, b: float

  while i < n:
    i += 1
    j = 0
    while j < 1_000:
      j += 0.01
      b += sin(i) + cos(j)
    cps jield()

  withLock L:
    echo id, ": ", b

when defined(gcArc):
  for i in 1..32:
    pool.work.addLast:
      whelp slow(i, 4)


  work(countProcessors())
else:
  echo "this example doesn't work outside --gc:arc"
