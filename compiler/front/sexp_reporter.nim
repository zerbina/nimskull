## Implementation of the CLI message generator

import
  experimental/[
    sexp,
    diff,
    colortext
  ],
  ast/[
    lineinfos,
    ast,
    reports
  ],
  front/[
    options,
    msgs
  ],
  std/[
    strutils
  ],
  ./reporter_common.nim


var writeConf: ConfigRef

import std/options as std_options

proc addFields[T](s: var SexpNode, r: T, ignore: seq[string] = @[])

proc sexp[T: object | tuple](obj: T): SexpNode =
  result = newSList()
  addFields(result, obj)

proc sexp[T: object | tuple](obj: ref T): SexpNode =
  result = newSList()
  addFields(result, obj[])

proc sexp*[E: enum](e: E): SexpNode = newSSymbol($e)

proc sexpItems*[T](s: T): SexpNode =
  result = newSList()
  for item in items(s):
    result.add sexp(item)


proc sexp*[T](s: seq[T]): SexpNode = sexpItems(s)
proc sexp*[R, T](s: array[R, T]): SexpNode = sexpItems(s)
proc sexp*[I](s: set[I]): SexpNode = sexpItems(s)
proc sexp*(s: cstring): SexpNode = sexp($s)

proc sexp*(v: SomeInteger): SexpNode = newSInt(BiggestInt(v))
proc sexp*(id: FileIndex): SexpNode =
  sexp(writeConf.formatPath(id))


# proc sexp*(id: ReportLineInfo): SexpNode =
#   sexp([
#     line = sexp(id.line),
#     filename =
#   ])

iterator sexpFields[T](obj: T, ignore: seq[string] = @[]): SexpNode =
  for name, value in fieldPairs(obj):
    var pass = true
    when value is ref or value is ptr:
      if isNil(value):
        pass = false

    when value is seq or value is string:
      if len(value) == 0:
        pass = false

    when value is TLineInfo:
      if pass and value == unknownLineInfo:
        pass = false

    when value is ReportLineInfo:
      if pass and value.isValid():
        pass = false

    if pass and name in ignore:
      pass = false

    if pass:
      yield newSKeyword(name, sexp(value))


func add*(other: var SexpNode, str: string, expr: SexpNode) =
  other.add newSSymbol(":" & str)
  other.add expr

proc sexp*[T](o: Option[T]): SexpNode =
  if o.isNone: newSNil() else: sexp(o.get())

proc addFields[T](s: var SexpNode, r: T, ignore: seq[string] = @[]) =
  for item in sexpFields(r, ignore):
    s.add item

proc sexp*(i: ReportLineInfo): SexpNode =
  result = newSList()
  result.addFields(i, @["file"])
  result.add newSKeyword(
    "file", writeConf.formatPath(i.file).sexp())

proc sexp*(i: TLineInfo): SexpNode =
  convertSexp([
    file = sexp(i.fileIndex),
    line = sexp(i.line),
    col = sexp(i.col)
  ])

proc sexp*(e: StackTraceEntry): SexpNode =
  result = newSList()
  result.addFields(e, @["filename"])
  result.add newSKeyword(
    "filename", writeConf.formatPath($e.filename).sexp())


proc sexp*(typ: PType): SexpNode =
  if typ.isNil: return newSNil()
  result = newSList()
  result.add newSSymbol(($typ.kind)[2 ..^ 1])
  if typ.sons.len > 0:
    result.add("sons", sexp(typ.sons))

proc sexp*(node: PNode): SexpNode =
  if node.isNil: return newSNil()

  result = newSList()
  result.add newSSymbol(($node.kind)[2 ..^ 1])
  case node.kind:
    of nkCharLit..nkUInt64Lit:    result.add sexp(node.intVal)
    of nkFloatLit..nkFloat128Lit: result.add sexp(node.floatVal)
    of nkStrLit..nkTripleStrLit:  result.add sexp(node.strVal)
    of nkSym:                     result.add newSSymbol(node.sym.name.s)
    of nkIdent:                   result.add newSSymbol(node.ident.s)
    else:
      for node in node.sons:
        result.add sexp(node)

proc sexp*(t: PSym): SexpNode =
  convertSexp([
    substr($t.kind, 2).newSSymbol(),
    name = sexp(t.name.s),
    info = sexp(t.info)
  ])

proc format(s: SexpNode): string =
  var r = addr result
  template add(arg: string): untyped =
    r[].add arg

  proc aux(s: SexpNode) =
    if s.isNil: return
    case s.kind:
      of SInt: add $s.getNum()
      of SString: add "\"" & s.getStr() & "\""
      of SFloat: add $s.getFNum()
      of SNil: add "nil"
      of SSymbol: add s.getSymbol()
      of SCons:
        add "("
        aux(s.car)
        add " . "
        aux(s.cdr)
        add ")"
      of SKeyword:
        add ":"
        add s.getKey()
        add " "
        aux(s.value)

      of SList:
        add "("
        var first = true
        for item in items(s):
          if not first: add " "
          first = false
          aux(item)

        add ")"

  aux(s)

proc reportHook*(conf: ConfigRef, r: Report): TErrorHandling =
  writeConf = conf
  let wkind = conf.writabilityKind(r)

  if wkind == writeDisabled:
    return

  else:
    var s = newSList()
    s.add newSSymbol(multiReplace($r.kind, {
      "rsem": "Sem",
      "rpar": "Par",
      "rlex": "Lex",
      "rint": "Int",
      "rext": "Ext",
      "rdbg": "Dbg",
      "rback": "Bck",
    }))
    s.add newSSymbol(":severity")
    s.add sexp(conf.severity(r))

    let f = @["kind"]

    case r.category:
      of repLexer:    s.addFields(r.lexReport, f)
      of repParser:   s.addFields(r.parserReport, f)
      of repCmd:      s.addFields(r.cmdReport, f)
      of repSem:
        if r.kind == rsemProcessingStmt:
          s.addFields(r.semReport, f & "node")

        else:
          s.addFields(r.semReport, f)

      of repDebug:    s.addFields(r.debugReport)
      of repInternal: s.addFields(r.internalReport)
      of repBackend:  s.addFields(r.backendReport)
      of repExternal: s.addFields(r.externalReport)

    if wkind == writeForceEnabled:
      echo s.format()

    else:
      conf.writeln(s.format())
