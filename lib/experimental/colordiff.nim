## This module implements formatting logic for colored text diffs - both
## multiline and inline.
##
## All formatting is generated in colored text format and can be later
## formatted in both plaintext and formatted manners using
## `colortext.toString`

import ./diff, ./colortext
import std/[sequtils, strutils, strformat, algorithm]

export toString, `$`, myersDiff, shiftDiffed

proc colorDollar*[T](arg: T): ColText = toColText($arg)

type
  DiffFormatConf* = object
    ## Diff formatting configuration
    maxUnchanged*: int ## Max number of the unchanged lines after which
    ## they will be no longer show. Can be used to compact large diffs with
    ## small mismatched parts.
    maxUnchangedWords*: int ## Max number of the unchanged words in a
    ## single line. Can be used to compact long lines with small mismatches
    showLines*: bool ## Show line numbers in the generated diffs
    lineSplit*: proc(str: string): seq[string] ## Split line
    ## into chunks for formatting
    sideBySide*: bool ## Show line diff with side-by-side (aka github
    ## 'split' view) or on top of each other (aka 'unified')
    explainInvisible*: bool ## If diff contains invisible characters -
    ## trailing whitespaces, control characters, escapes and ANSI SGR
    ## formatting - show them directly.
    explainWithUnicode*: bool ## Show mismatched characters as uicode
    ## equivalents or use ascii for formatting.
    inlineDiffSeparator*: ColText ## Text to separate words in the inline split
    formatChunk*: proc(text: string, mode, secondary: SeqEditKind): ColText ##  Format
    ## mismatched text. `mode` is the mismatch kind, `secondary` is used
    ## for `sekChanged` to annotated which part was deleted and which part
    ## was added.
    groupInline*: bool ## For inline edit operations - group cosecutive
    ## edit operations into single chunks.

  DiffFormatter* = object
    ## Item diff formatter - convert input value into formattable string,
    ## provide comparison proc for the the `diff` implementation.
    conf*: DiffFormatConf ## Text formatting configuration

proc chunk(
    conf: DiffFormatConf, text: string,
    mode: SeqEditKind, secondary: SeqEditKind = mode
  ): ColText =
  ## Format text mismatch chunk using `formatChunk` callback
  conf.formatChunk(text, mode, secondary)

func splitKeepSeparator*(str: string, sep: set[char] = {' '}): seq[string] =
  ## Default implementaion of the line splitter - split on `sep` characters
  ## but don't discard them - they will be present in the resulting output.
  var prev = 0
  var curr = 0
  while curr < str.len:
    if str[curr] in sep:
      if prev != curr:
        result.add str[prev ..< curr]

      prev = curr
      while curr < str.high and str[curr + 1] == str[curr]:
        inc curr

      result.add str[prev .. curr]
      inc curr
      prev = curr

    else:
      inc curr

  if prev < curr:
    result.add str[prev ..< curr]

proc formatDiffed*[T](
    ops: seq[SeqEdit],
    oldSeq, newSeq: seq[T],
    conf: DiffFormatConf
  ): tuple[oldLine, newLine: ColText] =
  ## Generate colored formatting fothe levenshtein edit operation using
  ## format configuration. Return old formatted line and new formatted line.

  var unchanged = 0
  var oldLine: seq[ColText]
  var newLine: seq[ColText]
  for idx, op in ops:
    case op.kind:
      of sekKeep:
        if unchanged < conf.maxUnchanged:
          oldLine.add conf.chunk(oldSeq[op.sourcePos], sekKeep)
          newLine.add conf.chunk(newSeq[op.targetPos], sekKeep)
          inc unchanged

      of sekDelete:
        oldLine.add conf.chunk(oldSeq[op.sourcePos], sekDelete)
        unchanged = 0

      of sekInsert:
        newLine.add conf.chunk(newSeq[op.targetPos], sekInsert)
        unchanged = 0

      of sekReplace:
        oldLine.add conf.chunk(oldSeq[op.sourcePos], sekReplace, sekDelete)
        newLine.add conf.chunk(newSeq[op.targetPos], sekReplace, sekInsert)
        unchanged = 0

      of sekNone:
        assert false

      of sekTranspose:
        discard

  return (
    oldLine.join(conf.inlineDiffSeparator),
    newLine.join(conf.inlineDiffSeparator)
  )




func visibleName(ch: char): tuple[unicode, ascii: string] =
  ## Get visible name of the character.
  case ch:
    of '\x00': ("␀", "[NUL]")
    of '\x01': ("␁", "[SOH]")
    of '\x02': ("␂", "[STX]")
    of '\x03': ("␃", "[ETX]")
    of '\x04': ("␄", "[EOT]")
    of '\x05': ("␅", "[ENQ]")
    of '\x06': ("␆", "[ACK]")
    of '\x07': ("␇", "[BEL]")
    of '\x08': ("␈", "[BS]")
    of '\x09': ("␉", "[HT]")
    of '\x0A': ("␤", "[LF]")
    of '\x0B': ("␋", "[VT]")
    of '\x0C': ("␌", "[FF]")
    of '\x0D': ("␍", "[CR]")
    of '\x0E': ("␎", "[SO]")
    of '\x0F': ("␏", "[SI]")
    of '\x10': ("␐", "[DLE]")
    of '\x11': ("␑", "[DC1]")
    of '\x12': ("␒", "[DC2]")
    of '\x13': ("␓", "[DC3]")
    of '\x14': ("␔", "[DC4]")
    of '\x15': ("␕", "[NAK]")
    of '\x16': ("␖", "[SYN]")
    of '\x17': ("␗", "[ETB]")
    of '\x18': ("␘", "[CAN]")
    of '\x19': ("␙", "[EM]")
    of '\x1A': ("␚", "[SUB]")
    of '\x1B': ("␛", "[ESC]")
    of '\x1C': ("␜", "[FS]")
    of '\x1D': ("␝", "[GS]")
    of '\x1E': ("␞", "[RS]")
    of '\x1F': ("␟", "[US]")
    of '\x7f': ("␡", "[DEL]")
    of ' ': ("␣", "[SPC]") # Space
    else: ($ch, $ch)

func toVisibleNames(str: string, unicode: bool): string =
  ## Convert all characters in the string into visible ones
  for ch in str:
    let (uc, ascii) = visibleName(ch)
    if unicode:
      result.add uc

    else:
      result.add ascii


func toVisibleNames(split: seq[string], unicode: bool): seq[string] =
  ## Convert all charactersw in all strings into visible ones.
  if 0 < split.len():
    for part in split:
      result.add toVisibleNames(part, unicode)

const Invis = { '\x00' .. '\x1F', '\x7F' }

func scanInvisible(text: string, invisSet: var set[char]): bool =
  ## Scan string for invisible characters from right to left, updating
  ## active invisible set as needed.
  var chIdx = text.high
  while 0 <= chIdx:
    if text[chIdx] in invisSet:
      return true

    else:
      invisSet = Invis

    dec chIdx

func hasInvisible(text: string, startSet: set[char] = Invis + {' '}): bool =
  ## Does string have significant invisible characters?
  var invisSet = startSet
  if scanInvisible(text, invisSet):
    return true

func hasInvisible(text: seq[string]): bool =
  ## Do any of strings in text have signfificant invisible characters.
  var idx = text.high
  var invisSet = Invis + {' '}
  while 0 <= idx:
    # Iterate over all items from righ to left - until we found first
    # visible character space is also considered significant, but removed
    # afterwards, so `" a"/"a"` is not considered to have invisible
    # characters.
    if scanInvisible(text[idx], invisSet):
      return true
    dec idx


func hasInvisibleChanges(diff: seq[SeqEdit], oldSeq, newSeq: seq[string]): bool =
  ## Is any change in the edit sequence invisible?
  var start = Invis + {' '}

  proc invis(text: string): bool =
    result = scanInvisible(text, start)

  # Iterate over all edits from right to left, updating active set of
  # invisible characters as we got.
  var idx = diff.high
  while 0 <= idx:
    let edit = diff[idx]
    case edit.kind:
      of sekDelete:
        if oldSeq[edit.sourcePos].invis():
          return true

      of sekInsert:
        if newSeq[edit.targetPos].invis():
          return true

      of sekNone, sekTranspose:
        discard

      of sekKeep:
        # Check for kept characters - this will update 'invisible' set if
        # any found, so edits like `" X" -> "X"` are not considered as 'has
        # invisible'
        if oldSeq[edit.sourcePos].invis():
          discard

      of sekReplace:
        if oldSeq[edit.sourcePos].invis() or
           newSeq[edit.targetPos].invis():
          return true

    dec idx

func diffFormatter*(): DiffFormatter =
  ## Default implementation of the diff formatter
  ##
  ## - split lines by whitespace
  ## - no hidden lines or workds
  ## - deleted: red, inserted: green, changed: yellow
  ## - explain invisible differences with unicode
  ## - convert to string using `$arg`
  ## - compare for equality using `==`
  DiffFormatter(
    conf: DiffFormatConf(
      # Don't hide inline edit lines
      maxUnchanged:       high(int),
      # Group edit operations for inline diff by default
      groupInline:        true,
      # Show differences if there are any invisible characters
      explainInvisible:   true,
      # Use unicode
      explainWithUnicode: true,
      # Don't hide inline edit words
      maxUnchangedWords:  high(int),
      showLines:          false,
      lineSplit:          (
        # Split by whitespace
        proc(a:    string): seq[string] = splitKeepSeparator(a)
      ),
      sideBySide:         false,
      formatChunk:        (
        proc(word: string, mode, secondary: SeqEditKind): ColText =
          case mode:
            of sekDelete:                word + fgRed
            of sekInsert:                word + fgGreen
            of sekKeep:                  word + fgDefault
            of sekReplace, sekTranspose: word + fgYellow
            of sekNone:                  word + fgDefault
      )
    )
  )

proc formatLineDiff*(
    old, new: string, conf: DiffFormatConf,
  ): tuple[oldLine, newLine: ColText] =
  ## Format single line diff into old/new line edits. Optionally explain
  ## all differences using options from `conf`

  let
    oldSplit = conf.lineSplit(old)
    newSplit = conf.lineSplit(new)
    diffed = levenshteinDistance[string](oldSplit, newSplit)

  var oldLine, newLine: ColText

  if conf.explainInvisible and (
     diffed.operations.hasInvisibleChanges(oldSplit, newSplit) or
     oldSplit.hasInvisible() or
     newSplit.hasInvisible()
  ):
    (oldLine, newLine) = formatDiffed(
      diffed.operations,
      oldSplit.toVisibleNames(conf.explainWithUnicode),
      newSplit.toVisibleNames(conf.explainWithUnicode),
      conf
    )

  else:
    (oldLine, newLine) = formatDiffed(
      diffed.operations,
      oldSplit, newSplit,
      conf
    )

  return (oldLine, newLine)


template groupByIt[T](sequence: seq[T], op: untyped): seq[seq[T]] =
  ## Group input sequence by value of the `op` into smaller subsequences
  var res: seq[seq[T]]
  var i = 0
  for item in sequence:
    if i == 0:
      res.add @[item]

    else:
      if ((block:
             let it {.inject.} = res[^1][0]; op)) ==
         ((block:
             let it {.inject.} = item; op)):
        res[^1].add item

      else:
        res.add @[item]

    inc i

  res

proc formatInlineDiff*(
    src, target: seq[string],
    diffed: seq[SeqEdit],
    conf: DiffFormatConf
  ): ColText =
  ## Format inline edit operations for `src` and `target` sequences using
  ## list of sequence edit operations `diffed`, formatting the result using
  ## `conf` formatter. Consecutive edit operations are grouped together if
  ## `conf.groupInline` is set to `true`

  var start = Invis + {' '}
  var chunks: seq[ColText]
  proc push(
      text: string,
      mode: SeqEditKind,
      secondary: SeqEditKind = mode,
      toLast: bool = false
    ) =
    ## Push single piece of changed text to the resulting chunk sequence
    ## after scanning for invisible characters. if `toLast` then add
    ## directly to the last chunk - needed to avoid intermixing edit
    ## visuals for the `sekReplace` edits which are the most important of
    ## them all
    var chunk: ColText
    if conf.explainInvisible and scanInvisible(text, start):
      chunk = conf.chunk(
        text.toVisibleNames(conf.explainWithUnicode), mode, secondary)

    else:
      chunk = conf.chunk(text, mode, secondary)

    if toLast:
      chunks[^1].add chunk

    else:
      chunks.add chunk

  let groups =
    if conf.groupInline:
      # Group edit operations by chunk - `[ins], [ins], [ins] -> [ins, ins, ins]`
      #
      # This is not specifically important for insertions and deletions,
      # but pretty much mandatory for the 'change' operation, if we don't
      # want to end up with the `h->He->El->Lo->O` instead of
      # `hello->HELLO`
      groupByIt(diffed, it.kind)

    else:
      # Treat each group as a single edit operation if needed
      mapIt(diffed, @[it])

  var gIdx = groups.high
  while 0 <= gIdx:
    case groups[gIdx][0].kind:
      of sekKeep:
        var buf: string
        for op in groups[gIdx]:
          buf.add src[op.sourcePos]

        push(buf, sekKeep)

      of sekNone, sekTranspose:
        discard

      of sekInsert:
        var buf: string
        for op in groups[gIdx]:
          buf.add target[op.targetPos]

        push(buf, sekInsert)

      of sekDelete:
        var buf: string
        for op in groups[gIdx]:
          buf.add src[op.sourcePos]

        push(buf, sekDelete)

      of sekReplace:
        var sourceBuf, targetBuf: string
        for op in groups[gIdx]:
          sourceBuf.add src[op.sourcePos]
          targetBuf.add target[op.targetPos]

        push(sourceBuf, sekReplace, sekDelete)
        # Force add directly to the last chunk
        push(targetBuf, sekReplace, sekInsert, toLast = true)

    dec gIdx

  # Because we iterated from right to left, all edit operations are placed
  # in reverse as well, so this needs to be fixed
  return chunks.reversed().join(conf.inlineDiffSeparator)


proc formatInlineDiff*(
    src, target: string, conf: DiffFormatConf
  ): ColText =
  ## Generate inline string editing annotation for the source and target
  ## string. Use `conf` for message mismatch configuration.
  let
    src = conf.lineSplit(src)
    target = conf.lineSplit(target)

  return formatInlineDiff(
    src, target, levenshteinDistance[string](src, target).operations, conf)

proc formatDiffed*(
    shifted: ShiftedDiff,
    oldSeq, newSeq: openarray[string],
    fmt: DiffFormatter = diffFormatter()
  ): ColText =

  var
    oldText, newText: seq[tuple[text: ColText, changed: bool]]
    lhsMax = 0

  let conf = fmt.conf

  let maxLhsIdx = len($shifted.oldShifted[^1].item)
  let maxRhsIdx = len($shifted.newShifted[^1].item)

  proc editFmt(edit: SeqEditKind, idx: int, isLhs: bool): ColText =
    if conf.showLines:
      let num =
        if edit == sekNone:
          alignRight(clt(" "), maxLhsIdx)

        elif isLhs:
          alignRight(clt($idx), maxLhsIdx)

        else:
          alignRight(clt($idx), maxRhsIdx)

      case edit:
        of sekDelete: "- " & num
        of sekInsert: "+ " & num
        of sekKeep: "~ " & num
        of sekNone: "? " & num
        of sekReplace: "-+" & num
        of sekTranspose: "^v" & num

    else:
      case edit:
        of sekDelete:
          conf.chunk("- ", sekDelete)
        of sekInsert:
          conf.chunk("+ ", sekInsert)
        of sekReplace:
          conf.chunk("-+", sekReplace)
        of sekKeep:
          conf.chunk("~ ", sekKeep)
        of sekTranspose:
          conf.chunk("^v", sekTranspose)
        of sekNone:
          conf.chunk((if isLhs: "? " else: "?"), sekNone)


  var unchanged = 0
  for (lhs, rhs, lhsDefault, rhsDefault, idx) in zipToMax(
    shifted.oldShifted, shifted.newShifted
  ):
    if lhs.kind == sekKeep and rhs.kind == sekKeep:
      if unchanged < conf.maxUnchanged:
        inc unchanged

      else:
        continue

    else:
      unchanged = 0

    oldText.add((editFmt(lhs.kind, lhs.item, true), true))

    newText.add((
      editFmt(rhs.kind, rhs.item, false),
      # Only newly inserted lines need to be formatted for the unified
      # diff, everything else is displayed on the 'original' version.
      not conf.sideBySide and rhs.kind in {sekInsert}
    ))

    var lhsEmpty, rhsEmpty: bool
    if not lhsDefault and
       not rhsDefault and
       lhs.kind == sekDelete and
       rhs.kind == sekInsert:

      let (oldLine, newLine) = formatLineDiff(
        oldSeq[lhs.item],
        newSeq[rhs.item],
        conf
      )

      oldText[^1].text.add oldLine
      newText[^1].text.add newLine


    elif rhs.kind == sekInsert:
      let tmp = newSeq[rhs.item]
      rhsEmpty = tmp.len == 0
      newText[^1].text.add conf.chunk(tmp, sekInsert)

    elif lhs.kind == sekDelete:
      let tmp = oldSeq[lhs.item]
      lhsEmpty = tmp.len == 0
      oldText[^1].text.add conf.chunk(tmp, sekDelete)

    else:
      let ltmp = oldSeq[lhs.item]
      lhsEmpty = ltmp.len == 0
      oldText[^1].text.add conf.chunk(ltmp, lhs.kind)

      let rtmp = newSeq[rhs.item]
      rhsEmpty = rtmp.len == 0
      newText[^1].text.add conf.chunk(rtmp, rhs.kind)


    if lhsEmpty and idx < shifted.oldShifted.high:
      oldText[^1].text.add toVisibleNames("\n", conf.explainWithUnicode)

    if rhsEmpty and idx < shifted.newShifted.high:
      newText[^1].text.add toVisibleNames("\n", conf.explainWithUnicode)

    lhsMax = max(oldText[^1].text.len, lhsMax)

  var first = true
  for (lhs, rhs) in zip(oldtext, newtext):
    if not first:
      # Avoid trailing newline of the diff formatting.
      result.add "\n"
    first = false

    if conf.sideBySide:
      result.add alignLeft(lhs.text, lhsMax + 3)
      result.add rhs.text

    else:
      result.add lhs.text
      if rhs.changed:
        result.add "\n"
        result.add rhs.text

proc formatDiffed*[T](
    oldSeq, newSeq: openarray[T],
    fmt: DiffFormatter,
    eqCmp: proc(a, b: T): bool = (proc(a, b: T): bool = a == b),
    strConv: proc(a: T): string = (proc(a: T): string = $a)
  ): ColText =

  formatDiffed(
    myersDiff(oldSeq, newSeq, eqCmp).shiftDiffed(oldSeq, newSeq),
    mapIt(oldSeq, strConv($it)),
    mapIt(newSeq, strConv(it)),
    fmt
  )


proc formatDiffed*(
    text1, text2: string,
    fmt: DiffFormatter = diffFormatter()
  ): ColText =
  ## Format diff of two text blocks via newline split and default
  ## `formatDiffed` implementation
  formatDiffed(text1.split("\n"), text2.split("\n"), fmt)

when isMainModule:
  if false:
    for (a, b) in @[
      ("1\n2", "1\n3"),
      ("word 1", "word 2"),
      ("word ", "word"),
      ("\e[32mword\e[39m", "\e[31mword\e[39m"),
      ("word\n", "word"),
      ("1\n2\n3\n4\n5\n", "1\n2\n3\n8\n9\n0\n\n"),
      ("", "\n"),
    ]:
      echo ">>>>"
      var fmt = diffFormatter()
      # fmt.explainWithUnicode = false
      fmt.conf.lineSplit = proc(line: string): seq[string] = mapIt(line, $it)
      fmt.conf.inlineDiffSeparator = clt(" ")
      fmt.conf.sideBySide = true
      echo formatDiffed(a, b, fmt)

    for (a, b) in @[
      ("""
  tundeclared_routine.nim(34, 17) Error: attempting to call routine: 'myiter'
    found tundeclared_routine.myiter(a: string) [iterator declared in tundeclared_routine.nim(32, 12)]
    found tundeclared_routine.myiter() [iterator declared in tuedeclared_routine.nim(33, 12)]
  tundeclared_routine.nim(34, 17) Error: expression has no type: myiter(1)
  tundeclared_routine.nim(39, 28) Error: invalid pragma: myPragma
  tundeclared_routine.nim(46, 14) Error: undeclared field: 'bar4' for type tundeclared_routine.Foo [type declared in tundeclared_routine.nim(43, 8)]
  tundeclared_routine.nim(46, 13) Error: expression has no type: `.`(a, bar3)
  tundeclared_routine.nim(51, 14) Error: undeclared field: 'bar4' for type tundeclared_routine.Foo [type declared in tundeclared_routine.nim(49, 8)]
  tundeclared_routine.nim(51, 13) Error: expression has no type: `.`(a, bar4)
  tundeclared_routine.nim(54, 11) Error: undeclared identifier: 'bad5'
  tundeclared_routine.nim(54, 15) Error: expression has no type: bad5(1)""", """
  tundeclared_routine.nim(34, 17) Error: attempting to call routine: 'myiter'
    found tundeclared_routine.myiter(a: string) [iterator declared in tundeclared_routine.nim(32, 12)]
    found tundeclared_routine.myiter() [iterator declared in tundeclared_routine.nim(33, 12)]
  tundeclared_routine.nim(34, 17) Error: expression has no type: myiter(1)
  tundeclared_routine.nim(39, 28) Error: invalid pragma: myPragma
  tundeclared_routine.nim(51, 13) Error: expression has no type: `.`(a, bar4)
  tundeclared_routine.nim(54, 11) Error: undeclared identifier: 'bad5'
  tundeclared_routine.nim(54, 15) Error: expression has no type: bad5(1)""")
    ]:
      echo ">>>>"
      var fmt = diffFormatter()
      fmt.conf.lineSplit = proc(line: string): seq[string] = mapIt(line, $it)
      let prev = fmt.conf.formatChunk
      fmt.conf.formatChunk = proc(text: string, mode, secondary: SeqEditKind): ColText =
                               if mode == sekReplace:
                                 prev(text, secondary, secondary) + styleReverse

                               else:
                                 prev(text, mode, mode)

      echo formatDiffed(a, b, fmt)

when isMainModule:
  # Configure diff formattter to use no unicode or colors to make testing
  # easier. Each inserted/deleted chunk is annotated with `D/I/R/K` for the
  # Delete/Insert/Replace/Keep respectively, and wrapped in the `[]`. Line
  # split is done on each whitespace and elements are joined using `#`
  # character.
  var fmt = diffFormatter()
  fmt.conf.explainWithUnicode = false
  fmt.conf.inlineDiffSeparator = clt("#")
  fmt.conf.formatChunk = proc(
    word: string, mode, secondary: SeqEditKind
  ): ColText = &"[{($mode)[3]}/{word}]" + fgDefault

  proc diff(a, b: string, sideBySide: bool = false): string =
    fmt.conf.sideBySide = sideBySide
    return formatDiffed(a, b, fmt).toString(false)

  proc ediff(a, b: string): string =
    let oldFormat = fmt.conf.formatChunk
    fmt.conf.formatChunk = proc(
      word: string, mode, secondary: SeqEditKind
    ): ColText =
      if mode == sekReplace:
        if secondary == sekDelete:
           &"[R/<{word}>-" + fgDefault
        else:
           &"<{word}>]" + fgDefault

      else:
        &"[{($mode)[3]}/{word}]" + fgDefault

    let edit = formatInlineDiff(a, b, fmt.conf)
    fmt.conf.formatChunk = oldFormat
    return edit.toString(false)

  proc ldiff(a, b: string): (string, string) =
    let (old, new) = formatLineDiff(a, b, fmt.conf)
    return (old.toString(false), new.toString(false))

  doAssert not hasInvisible(" a")
  doAssert hasInvisible("a ")
  doAssert hasInvisible("a \n")
  doAssert not hasInvisible("a a")
  doAssert hasInvisible("a\n")

  proc assertEq(found, expected: string) =
    if found != expected:
      assert false, &"expected:\n{expected}\nfound:\n{found}\ndiff:\n{diffText(expected, found, true)}"

  proc assertEq(lhs, rhs: (string, string)) =
    assertEq(lhs[0], rhs[0])
    assertEq(lhs[1], rhs[1])

  diff("a", "b").assertEq:
    """
[D/- ][R/a]
[I/+ ][R/b]"""
    # `-` and `+` are formatted as delete/insert operations, `a` is formatted as `Replace`

  diff("a b", "b b").assertEq:
    """
[D/- ][R/a]#[K/ ]#[K/b]
[I/+ ][R/b]#[K/ ]#[K/b]"""
    # `Keep` the space and last `b`, replace first `a -> b`. Space is in
    # the middle of the diff, so it is not considered 'invisible' and not
    # highlighted explicitly.

  diff("", "\n", true).assertEq:
    """
[K/~ ][K/]   [K/~ ][K/][LF]
[N/? ]       [I/+ ][I/]"""

    # Keep the empty line. `[LF]` at the end is not considered for diff
    # since it used to *separate* lines.

  diff("a ", "a").assertEq:
    """
[D/- ][K/a]#[D/[SPC]]
[I/+ ][K/a]"""
    # Deleted trailing space

  # Missing leading whitespace is not considered an 'invisible' character
  # for both regular and line diffs.
  diff(" a", "a", true).assertEq("[D/- ][D/ ]#[K/a]   [I/+ ][K/a]")
  ldiff(" a", "a").assertEq(("[D/ ]#[K/a]", "[K/a]"))
  # Intermediate whitespace is not invisible as well
  ldiff("a a", "a").assertEq(("[D/a]#[D/ ]#[K/a]", "[K/a]"))
  # Trailing whitespace IS invisible
  ldiff("a ", "a").assertEq(("[K/a]#[D/[SPC]]", "[K/a]"))

  # Control characters ARE invisible, regardless of their position in the
  # text, so they are explicitly shown in diffs
  ldiff("\ea", "a").assertEq(("[R/[ESC]a]", "[R/a]"))

  # Inline edit diff annotations - for spelsuggest, invalid CLI switches,
  # misspelled words, spell annotations, high-granularity diff suggestions.
  ediff("a", "b").assertEq("[R/<a>-<b>]") # Replace 'a' with 'b'

  # Replace first 'a', delete second one. Edit streaks are grouped
  ediff("a a", "b").assertEq("[R/<a>-<b>]#[D/ a]")
  # Elements between blocks are joined with `#` character, just like
  # regular inline diff elements
  ediff("w o r d", "w e r d").assertEq("[K/w ]#[R/<o>-<e>]#[K/ r d]")
