## Very basic tool that extracts some information from execution traces.

import ../compiler/ic/rodfiles
import ../compiler/ast/lineinfos
import ../compiler/mir/exectraces
import ../compiler/utils/containers

import std/[os,strutils,algorithm]

import std/private/miscdollars

proc main() =
  let dbFile = paramStr(1)
  let traceout = paramStr(2)

  var paths: seq[string]

  var file = rodfiles.open(dbFile)
  file.loadHeader()
  file.loadSection(topLevelSection)

  var db: TraceDb

  var len = 0
  file.loadPrim len
  for x in 0..<len:
    var str: string
    file.loadPrim str
    paths.add str
  file.loadPrim db

  file.close()

  var hits: seq[(TraceId, int)]

  var f = open(traceout, fmRead)
  for line in f.lines():
    hits.add (hits.len.TraceId, parseInt(line))

  sort(hits, proc(a, b: auto): int = b[1] - a[1])

  for i in 0..<min(hits.len, 100):
    let it = hits[i]
    let info = db.locations[TraceId(it[0])]

    var str: string
    str.toLocation(paths[info.fileIndex.int], info.line.int, info.col.int + 1)
    echo "#", i+1, " block at: ", str, " with ", it[1], " visits; id: ", it[0].int

  var numDark = 0
  for i, (_, it) in hits.pairs:
    if it == 0:
      # let info = db.locations[TraceId(i)]
      # var str: string
      # str.toLocation(paths[info.fileIndex.int], info.line.int, info.col.int + 1)
      # echo "not reached: ", str
      inc numDark

  echo hits.len
  echo db.locations.len

  echo "#dark: ", numDark, " (", numDark / db.locations.len * 100, "%)"

main()