import compiler/ast/ast_types
import compiler/utils/idioms
import std/[hashes, intsets]

from compiler/ast/ast import GrowthFactor, StartSize, id

type
  TIdentIter* = object
    ## Iterator over all symbols with same identifier
    h*: Hash      ## current hash
    name*: PIdent

  TTabIter* = object
    i: Hash

proc mustRehash(length, counter: int): bool =
  assert length > counter, "table not initialized?"
  result = (length * 2 < counter * 3) or (length - counter < 4)

proc nextTry(h, maxHash: Hash): Hash =
  result = ((5 * h) + 1) and maxHash
  # For any initial h in range(maxHash), repeating that maxHash times
  # generates each int in range(maxHash) exactly once (see any text on
  # random-number generation for proof).

template isFilled(x: TabEntry): bool = x.sym != nil

proc initSymbolTable*(): SymbolTable =
  newSeq(result.data, StartSize)

proc contains*(t: SymbolTable, n: PSym): bool =
  var h: Hash = n.name.h and high(t.data) # start with real hash value
  while isFilled(t.data[h]):
    if t.data[h].sym == n:
      return true
    h = nextTry(h, high(t.data))
  result = false

proc rawInsert(data: var openArray[TabEntry], e: TabEntry) =
  var h: Hash = e.sym.name.h and high(data)
  while isFilled(data[h]):
    if data[h].sym == e.sym:
      # allowed for 'export' feature:
      #InternalError(n.info, "StrTableRawInsert: " & n.name.s)
      return
    h = nextTry(h, high(data))
  assert not isFilled(data[h])
  data[h] = e

proc replaceRaw(data: var openArray[TabEntry], prev, n: PSym) =
  assert prev.name.h == prev.name.h
  var h: Hash = prev.name.h and high(data)
  while isFilled(data[h]):
    if data[h].sym == prev:
      data[h].sym = n
      return
    h = nextTry(h, high(data))

  unreachable("nothing to replace")

proc replace*(t: var SymbolTable, prevSym, newSym: PSym) =
  replaceRaw(t.data, prevSym, newSym)

proc enlarge(t: var SymbolTable) =
  var n: seq[TabEntry]
  newSeq(n, t.data.len * GrowthFactor)
  for i in 0..high(t.data):
    if isFilled(t.data[i]): rawInsert(n, t.data[i])
  swap(t.data, n)

proc add*(t: var SymbolTable, n: PSym, time: uint32) =
  if mustRehash(t.data.len, t.counter):
    enlarge(t)
  rawInsert(t.data, (n, time))
  inc t.counter

proc inclReportConflict*(t: var SymbolTable, n: PSym, time: uint32;
                         onConflictKeepOld = false): PSym =
  # if `t` has a conflicting symbol (same identifier as `n`), return it
  # otherwise return `nil`. Incl `n` to `t` unless `onConflictKeepOld = true`
  # and a conflict was found.
  #assert n.name != nil
  var
    h: Hash = n.name.h and high(t.data)
    replaceSlot = -1

  while true:
    let it = t.data[h]
    if not isFilled(it):
      break
    # Semantic checking can happen multiple times thanks to templates
    # and overloading: (var x=@[]; x).mapIt(it).
    # So it is possible the very same sym is added multiple
    # times to the symbol table which we allow here with the 'it == n' check.
    if it.sym.name.id == n.name.id:
      if it.sym == n:
        return nil
      replaceSlot = h
    h = nextTry(h, high(t.data))

  if replaceSlot >= 0:
    # the symbol already exists in the table
    result = t.data[replaceSlot].sym
    if not onConflictKeepOld:
      t.data[replaceSlot].sym = n # oevrwrite it with the newer definition!
    return result # but return the old one
  elif mustRehash(t.data.len, t.counter):
    enlarge(t)
    rawInsert(t.data, (n, time))
  else:
    assert not isFilled(t.data[h])
    t.data[h] = (n, time)

  inc(t.counter)
  result = nil

proc incl*(t: var SymbolTable, n: PSym, time: uint32;
           onConflictKeepOld = false): bool {.discardable.} =
  result = inclReportConflict(t, n, time, onConflictKeepOld) != nil

proc get*(t: SymbolTable, name: PIdent): PSym =
  var h: Hash = name.h and high(t.data)
  while true:
    let it = t.data[h]
    if not isFilled(it):
      break
    if it.sym.name.id == name.id:
      return it.sym
    h = nextTry(h, high(t.data))

  result = nil # not found

proc nextIdentIter*(ti: var TIdentIter, tab: SymbolTable): PSym =
  var h = ti.h and high(tab.data)
  var start = h
  result = tab.data[h].sym
  while result != nil:
    if result.name.id == ti.name.id: break
    h = nextTry(h, high(tab.data))
    if h == start:
      result = nil
      break
    result = tab.data[h].sym
  ti.h = nextTry(h, high(tab.data))

proc initIdentIter*(ti: var TIdentIter, tab: SymbolTable, name: PIdent): PSym =
  ti.h = name.h
  ti.name = name
  if tab.counter == 0: result = nil
  else: result = nextIdentIter(ti, tab)

proc nextIdentExcluding*(ti: var TIdentIter, tab: SymbolTable,
                         excluding: IntSet): PSym =
  var h: Hash = ti.h and high(tab.data)
  var start = h
  result = tab.data[h].sym
  while result != nil:
    if result.name.id == ti.name.id and not contains(excluding, result.id):
      break
    h = nextTry(h, high(tab.data))
    if h == start:
      result = nil
      break
    result = tab.data[h].sym
  ti.h = nextTry(h, high(tab.data))
  if result != nil and contains(excluding, result.id): result = nil

proc firstIdentExcluding*(ti: var TIdentIter, tab: SymbolTable, s: PIdent,
                          excluding: IntSet): PSym =
  ti.h = s.h
  ti.name = s
  if tab.counter == 0: result = nil
  else: result = nextIdentExcluding(ti, tab, excluding)


proc nextIter*(ti: var TTabIter, tab: SymbolTable): PSym =
  result = nil
  # move the iterator to the next filled slot (if one exists)
  while ti.i < tab.data.len:
    let it = tab.data[ti.i]
    inc ti.i                 # ... and increment by one always
    if isFilled(it):
      return it.sym

proc initTabIter*(ti: var TTabIter, tab: SymbolTable): PSym =
  ti.i = 0
  result =
    if tab.counter == 0: nil
    else:                nextIter(ti, tab)

iterator items*(tab: SymbolTable): PSym =
  var it: TTabIter
  var s = initTabIter(it, tab)
  while s != nil:
    yield s
    s = nextIter(it, tab)