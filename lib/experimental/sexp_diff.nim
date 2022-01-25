import
  ./sexp,
  ./colortext,
  ./colordiff,
  std/[
    strformat,
    sequtils,
    strutils,
    tables,
    intsets,
    options,
    algorithm
  ]

type IdxCostMap* = Table[(int, int), int]

proc stablematch*[T](
    lhs, rhs: seq[T], weight: proc(a, b: int): int,
    order: SortOrder = SortOrder.Ascending
  ): tuple[lhsIgnore, rhsIgnore: seq[int], map: IdxCostMap] =
  ## Do a weighted matching of the items in lhs and rhs sequences using
  ## weight function. Return most cost-effective matching elements.

  var lfree: seq[int]
  var canTry: Table[int, seq[int]]
  var rmap: Table[int, (int,int)]

  for idx in 0 ..< len(lhs):
    lfree.add idx

  for l in lfree:
    canTry[l] = @[]
    for r in 0 ..< len(rhs):
      canTry[l].add r

  proc getCost(l, r: int, res: var IdxCostMap): int =
    if (l, r) notin res:
      res[(l, r)] = weight(l, r)

    res[(l, r)]

  var tmp: IdxCostMap
  while 0 < len(lfree):
    let l = lfree.pop()
    if 0 < canTry[l].len:
      let r = canTry[l].pop()
      if r in rmap:
        let (oldL, _) = rmap[r]
        let tryCost = getCost(l, r, tmp)
        let otherCost = getCost(oldL, r, tmp)
        let better =
          if order == Ascending:
            otherCost < tryCost
          else:
            otherCost > tryCost

        if better:
          lfree.add oldL
          rmap[r] = (l, r)

        else:
          lfree.add l

      else:
        discard getCost(l, r, tmp)
        rmap[r] = (l, r)

  var lset: IntSet
  for idx in 0 ..< len(rhs):
    if idx in rmap:
      lset.incl rmap[idx][0]
      result.map[rmap[idx]] = tmp[rmap[idx]]

    else:
      result.rhsIgnore.add idx

  for idx in 0 ..< len(lhs):
    if idx notin lset:
      result.lhsIgnore.add idx


proc sortedStablematch*[T](
    lhs, rhs: seq[T], weight: proc(a, b: int): int,
    order: SortOrder = SortOrder.Ascending
  ): tuple[
    lhsIgnore, rhsIgnore: seq[int],
    ordered: seq[tuple[pair: (int, int), cost: int]]
  ] =

  var map: IdxCostMap
  (result.lhsIgnore, result.rhsIgnore, map) = stablematch(
    lhs, rhs, weight, order
  )

  result.ordered = toSeq(pairs(map)).sortedByIt(it[1])

export `$`, toString

type
  SexpPathPartKind = enum
    spIndex
    spKey

  SexpPathPart = object
    case kind*: SexpPathPartKind
      of spIndex:
        index*: int

      of spKey:
        key*: string

  SexpPath* = seq[SexpPathPart]

  SexpMismatchKind* = enum
    smMissingKey
    smDifferentLiteral
    smDifferentSymbol
    smArrayLen
    smKindMismatch

  SexpMismatch* = object
    path*: SexpPath
    case kind*: SexpMismatchKind
      of smMissingKey:
        key*: string

      of smDifferentLiteral, smKindMismatch, smArrayLen, smDifferentSymbol:
        expected*, found*: SexpNode
        arraydiff*: tuple[target, input: seq[int]]

func part(key: string): SexpPathPart =
  SexpPathPart(key: key, kind: spKey)

func part(index: int): SexpPathPart =
  SexpPathPart(index: index, kind: spIndex)


func mismatch(path: SexpPath, key: string): SexpMismatch =
  SexpMismatch(kind: smMissingKey, key: key, path: path)

func mismatch(
    kind: SexpMismatchKind, path: SexpPath,
    expected, found: SexpNode
  ): SexpMismatch =

  result = SexpMismatch(kind: kind, path: path)
  result.expected = expected
  result.found = found


func diff*(target, input: SexpNode): seq[SexpMismatch] =
  proc aux(
      target, input: SexpNode,
      path: SexpPath,
      mismatches: var seq[SexpMismatch]
    ) =

    if target.kind == SSymbol and target.getSymbol() == "_":
      # `_` matches against everything and does not produce diffs
      return

    elif target.kind != input.kind:
      mismatches.add mismatch(smKindMismatch, path, target, input)

    else:
      case target.kind:
        of SInt:
          if target.getNum() != input.getNum():
            mismatches.add mismatch(smDifferentLiteral, path, target, input)

        of SFloat:
          if target.getFNum() != input.getFNum():
            mismatches.add mismatch(smDifferentLiteral, path, target, input)

        of SString:
          if target.getStr() != input.getStr():
            mismatches.add mismatch(smDifferentLiteral, path, target, input)

        of SSymbol:
          if target.getSymbol() != input.getSymbol():
            mismatches.add mismatch(smDifferentSymbol, path, target, input)

        of SList:
          var
            inputKeys: Table[string, int]
            inputNonKeys, targetNonKeys: seq[int]

          for idx, item in pairs(input):
            if item.kind == SKeyword:
              inputKeys[item.getKey()] = idx

            else:
              inputNonKeys.add idx

          for idx, item in pairs(target):
            if item.kind == SKeyword:
              let key = item.getKey()
              if key in inputKeys:
                aux(item, input[inputKeys[key]], path & part(key), mismatches)

              else:
                mismatches.add mismatch(path, key)

            else:
              targetNonKeys.add idx

          if inputNonKeys.len != targetNonKeys.len:
            var mis =  mismatch(smArrayLen, path, target, input)
            mis.arraydiff = (targetNonKeys, inputNonKeys)
            mismatches.add mis

          for idx in 0 ..< min(inputNonKeys.len, targetNonKeys.len):
            aux(
              target[targetNonKeys[idx]],
              input[inputNonKeys[idx]],
              path & part(inputNonKeys[idx]),
              mismatches
            )

        of SCons:
          aux(target.car, input.car, path & part(0), mismatches)
          aux(target.cdr, input.cdr, path & part(1), mismatches)

        of SNil:
          discard

        of SKeyword:
          aux(target.value, input.value, path, mismatches)


  aux(target, input, @[], result)

func formatPath(path: SexpPath): string =
  if path.len == 0:
    result = "<root>"

  else:
    for part in path:
      case part.kind:
        of spIndex:
          result.add "[" & $part.index & "]"

        of spKey:
          result.add ":" & part.key

proc describeDiff*(diff: seq[SexpMismatch], conf: DiffFormatConf): ColText =
  coloredResult()

  for idx, mismatch in diff:
    if 0 < idx:
      add "\n"

    add formatPath(mismatch.path) + fgYellow
    case mismatch.kind:
      of smKindMismatch:
        add " expected kind '", $mismatch.expected.kind + fgGreen
        add "', but got '", $mismatch.found.kind + fgRed
        add "'"

      of smMissingKey:
        add " misses key ", mismatch.key + fgRed

      of smDifferentLiteral, smDifferentSymbol:
        let exp = $mismatch.expected
        let got = $mismatch.found
        add " expected ", exp + fgGreen
        add ", but got ", got + fgRed
        if '\n' notin exp and '\n' notin got:
          add " ("
          add getEditVisual(exp, got, conf)
          add ")"

      of smArrayLen:
        add " len mismatch. Expected ", $mismatch.expected.len + fgGreen
        add " elements , but got ", $mismatch.found.len + fgRed

proc sdiff(target, input: string): Option[ColText] =
  let (target, input) = (target.parseSexp(), input.parseSexp())
  let diff = diff(target, input)
  if 0 < len(diff):
    return some diff.describeDiff(diffFormatter[string]().conf)

proc sortd(r: tuple[expectedReports, givenReports: seq[SexpNode]]) =
  var diffMap = TableRef[(int, int), seq[SexpMismatch]]()
  proc reportCmp(a, b: int): int =
    # Best place for further optimization and configuration - if more
    # comparison speed isneeded, try starting with error kind, file, line
    # comparison, they doing a regular msg != msg compare and only then
    # deep structural diff.
    echo "comparing reports >>>"
    echo "exp: ", r.expectedReports[a]
    echo "giv: ", r.givenReports[b]
    if r.expectedReports[a][0] != r.givenReports[b][0]:
      result += 10

    let diff = diff(r.expectedReports[a], r.givenReports[b])
    diffMap[(a, b)] = diff
    result += diff.len
    echo "cost: ", result
    echo "<<<"

  let (lhs, rhs, order) = sortedStablematch(
    r.expectedReports, r.givenReports, reportCmp, Ascending)

  var result: ColText
  coloredResult()

  var first = true
  proc addl() =
    if not first:
      add "\n"

    first = false


  var
    conf = diffFormatter[string]().conf

  for (pair, weight) in order:
    echo pair, weight
    if 0 < weight:
      addl()
      addl()
      add "Expected:\n\n- $1\n\nGiven:\n\n+ $2\n\n" % [
        r.expectedReports[pair[0]].toLine(),
        r.givenReports[pair[1]].toLine()
      ]

      add diffMap[pair].describeDiff(conf).indent(2)

  for exp in lhs:
    addl()
    addl()
    add "Missing expected annotation:\n\n"
    add "? ", r.expectedReports[exp].toLine()
    add "\n\n"

  for give in rhs:
    addl()
    addl()
    add "Unexpected given annotation:\n\n"
    add "? ", r.expectedReports[give].toLine()
    add "\n\n"

  echo result


when isMainModule:
  sortd(( @[
    parseSexp("""(User :str "Another hint" :location ("tfile.nim" 11 7) :severity Hint)"""),
    parseSexp("""(User :str "User hint" :location ("tfile.nim" 8 _))""")
  ], @[
    parseSexp("""(User :severity Hint :str "User hint" :location ("tfile.nim" 9 6))"""),
    parseSexp("""(User :severity Hint :str "Another hint" :location ("tfile.nim" 11 6))""")
  ] ))

when isMainModule and false:
  for str in @[
    ("1", "2"),
    ("(:line 12 :col 10)", "(:line 30 :col 30)"),
    ("(Kind :expr 12)", "(Kind :expr 39)"),
    ("(Kind :expr 12)", "(Kind)"),
    ("(SymA :expr 12)", "(SymB :expr 12)")
  ]:
    let diff = sdiff(str[0], str[1])
    if diff.isSome():
      echo "```diff"
      echo "- ", str[0]
      echo "+ ", str[1]
      echo diff.get()
      echo "```\n"
