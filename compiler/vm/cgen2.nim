## `vmir`-based C code-generator. Separated into two phases:
## * code-gen: IR -> CAst, CDecl
## * emit: write CAst and CDecl to file

import
  std/[
    hashes,
    packedsets,
    sets,
    strformat,
    tables
  ],

  compiler/ast/[
    ast_types,
    ast_query
  ],
  compiler/front/[
    options,
    msgs
  ],
  compiler/ic/[
    bitabs
  ],
  compiler/utils/[
    int128,
    pathutils,
    ropes
  ],
  compiler/vm/[
    irtypes,
    vmir,
    irdbg
  ]

from compiler/vm/vmdef import unreachable
from compiler/vm/vmaux import getEnvParam

from compiler/vm/irpasses import computeTypes, PassError

type
  TypeKey = TypeId

  TypeSet = Table[int, TypeId] # TODO: only store unique types?
  SymSet = Table[int, SymId] # TODO: use a `HashSet`

  LocalGenCtx = object
    ## Mutable environmental state that only applies to the current item
    ## (routine) that is being code-gen'ed

  ModuleCtx = object
    ## Environmental state that is local to the module the IR being processed
    ## lies in.

    types: PackedSet[TypeId] # all used type for the module

    syms: PackedSet[SymId] ## all used symbols that need to be declared in the C code. # TODO: should be a SymSet
    funcs: PackedSet[ProcId] ## all used functions that need to be declared in the C code

    # TODO: header paths can be very regular. Maybe a CritBitTree[void} would make sense here?
    # TODO: the header includes are currently emitted in an arbitrary order, is that okay? (check the old cgen)
    headers: HashSet[string] ## all headers the module depends on

  # TODO: rename
  FuncId = distinct uint32


  CAstNodeKind = enum
    ## Syntactic node
    # TODO: reorder
    cnkError # XXX: temporary. used to encode missing code-generator logic in the output
    cnkStmtList

    cnkIf
    cnkWhile
    cnkSwitch
    cnkCase
    cnkCall
    cnkReturn
    cnkGoto

    cnkBraced # braced anonymous initializer

    cnkCast

    cnkLabel # a "label x"

    cnkDotExpr

    cnkStrLit # string literal
    cnkIntLit

    cnkDef
    cnkType
    cnkTernary
    cnkInfix
    cnkPrefix
    cnkIdent
    cnkBracket

  # XXX: hmm, 3 byte wasted for padding
  CAst = seq[tuple[kind: CAstNodeKind, a, b: uint32]]

  # TODO: use the correct names for the syntax constructs
  CDeclAstNodeKind = enum
    ## Basic AST for describing both the content of structs and types in C.
    ## Not really a syntax tree.
    cdnkStruct
    cdnkField # type-decl + ident
    cdnkUnion

    cdnkEmpty

    cdnkType # references another type via a ``CTypeId``
    cdnkWeakType # a "weak" reference to a type, meaning that a definition of
                 # the type doesn't have to be present in the translation unit

    cdnkIntLit # a unsigned integer literal (`a` encodes the low and `b` the high bits)

    cdnkFuncPtr # function-ptr type decl
    cdnkPtr # XXX: strictly speaking, the `*` is part of the declarator and not of the specifier
    cdnkBracket
    cdnkIdent

  CDecl = seq[tuple[kind: CDeclAstNodeKind, a, b: uint32]]

  CTypeDesc = distinct CDecl


  CTypeId = TypeId

  CIdent = LitId ## An identifier in the generated code

  CTypeInfo = object
    decl: CDecl
    name: CIdent #

  CProcHeader = object
    ident: CIdent

    returnType: CTypeId
    args: seq[tuple[typ: CTypeId, name: CIdent]]

  IdentCache = BiTable[string]

  CTypeNode = object
    # TODO: encode whether the type is a pointer via the `name` field
    case isPtr: bool
    of true: nil
    of false:
      name: CIdent

    isImmutable: bool # TODO: merge both bools into a `set`
    isVolatile: bool

  GlobalGenCtx* = object
    ## Environment state that applies to all to all code, independent from
    ## which routine or module the code is in.

    # TODO: BiTable might not be the best choice. It recomputes the hash for the
    #       key on each entry comparision, since it doesn't store key hashes.
    #       `idents.IdentCache` could be used here, but it's very tailored to Nim (and
    #       also a `ref` type). Maybe a hash-table overlay (see
    #       ``vmdef.TypeTable``) is a better choice here
    idents: IdentCache # identifiers used in the generated C-code
    strings: BiTable[string]

    rttiV1: Table[TypeKey, CIdent] # run-time-type-information requested by the IR being processed.
    rttiV2: Table[TypeKey, CIdent]

    funcMap: Table[int, int] ## symbol-id -> index into `procs` # TODO: a table is maybe the wrong data structure here.
    funcs: seq[CProcHeader]

    ctypes: seq[CTypeInfo] #


  CAstBuilder = object
    ast: CAst

const VoidCType = CTypeId(0)
const StringCType = CTypeId(1)

const InvalidCIdent = CIdent(0) # warning: this depends on a implementation detail of `BiTable`

#[
func hash(a: TypeKey): Hash =
  hash(TypeId(a).itemId)
func `==`(a, b: TypeKey): bool =
  a.PType.itemId == b.PType.itemId
]#

func `==`(a, b: CTypeId): bool {.borrow.}

func mangledName(sym: PSym): string =
  # TODO: cache the mangled names (and don't use TLoc for it!)
  # TODO: implement
  if {sfImportc, sfExportc} * sym.flags != {}:
    $sym.loc.r
  else:
    sym.name.s

func mangledName(d: Declaration): string =
  # XXX: temporary
  d.name

const BaseName = "Sub" ## the name of the field for the base type

func add(decl: var CDecl, k: CDeclAstNodeKind; a, b: uint32 = 0) =
  decl.add((k, a, 0'u32))

func addField(decl: var CDecl, typ: CTypeId, name: CIdent) =
  decl.add cdnkField
  decl.add cdnkType, typ.uint32
  decl.add cdnkIdent, name.uint32

func addField(decl: var CDecl, cache: var IdentCache, typ: CTypeId, name: sink string) {.inline.} =
  decl.addField(typ, cache.getOrIncl(name))

func addIntLit(decl: var CDecl, i: uint64) {.inline.} =
  decl.add cdnkIntLit, uint32(i and 0xFFFFFFFF'u64), uint32(i shr 32)

type CTypeMap = Table[TypeKey, CTypeId]

type TypeGenCtx = object
  # inherited state
  cache: IdentCache
  env: ptr IrEnv

  # non-inherited state
  weakTypes: set[TypeNodeKind] # the set of types that can be turned into forward declarations when declared as a pointer

func requestType(c: var TypeGenCtx, t: TypeId): CTypeId =
  ## Requests the type-id for `t`. If the c-type for `t` doesn't exist yet, a
  ## slot for it is reserved and it's added to the `c.forwared` list
  CTypeId(t)

func requestFuncType(c: var TypeGenCtx, t: TypeId): CTypeId =
  # XXX: this is going to be tricky
  discard

func genRecordNode(c: var TypeGenCtx, decl: var CDecl, i: var RecordNodeIndex, fstart: int): int =
  let n = c.env.types[i]
  inc i

  case n.kind
  of rnkList:
    discard "ignore"
    for _ in 0..<n.len:
      result += genRecordNode(c, decl, i, fstart)

  of rnkFields:
    for i in n.a..n.b:
      let f = fstart + i.int
      let
        field = c.env.types.field(f)
        name =
          if field.sym == NoneSymbol:
            # note: ignoring the records field offset means that unnamed
            #       fields in ``object`` types using inheritance won't work
            fmt"Field{i}"
          else:
            c.env.syms[field.sym].decl.name

      decl.addField(c.cache,
                    c.requestType(field.typ),
                    name)

    result = int(n.b - n.a + 1)

  of rnkCase:
    # TODO: properly name the generated fields, unions, and structs
    #[let discrField = c.env.types.field(f)
    decl.addField(c.cache, c.requestType(discrField.typ), c.env.syms[discrField.sym].decl.name)
    ]#

    discard genRecordNode(c, decl, i, fstart) # discriminator; needs to come before the union

    decl.add cdnkUnion, n.len - 1
    decl.add cdnkEmpty
    for _ in 1..<n.len:
      discard genRecordNode(c, decl, i, fstart)

    result = 2 # discriminator field + union

  of rnkBranch:
    let start = decl.len
    decl.add cdnkStruct
    decl.add cdnkEmpty

    let count = genRecordNode(c, decl, i, fstart)
    decl[start].a = count.uint32

    result = 1 # a single struct

  else:
    unreachable(n.kind)


func addWeakType(dest: var CDecl, c: var TypeGenCtx, t: TypeId) =
  # don't use a weak-dependency for ptr-like types
  let kind =
    if c.env.types[t].kind in c.weakTypes: cdnkWeakType
    else: cdnkType

  dest.add kind, c.requestType(t).uint32

func genCTypeDecl(c: var TypeGenCtx, t: TypeId): CDecl =
  case c.env.types[t].kind
  of tnkRecord:
    let kind =
      if false #[tfUnion in t.flags]#: cdnkUnion
      else:                  cdnkStruct

    result.add kind, 0#, cast[uint32](t.flags)
    result.add cdnkEmpty

    # base type
    if (let base = c.env.types.baseType(t); base != NoneType):
      result.addField(c.cache, c.requestType(base), BaseName)
      inc result[0].a

    var i = c.env.types[t].record.toIndex.RecordNodeIndex
    let f = c.env.types[t].a.int
    let count = genRecordNode(c, result, i, f)
    result[0].a += count.uint32

  of tnkArray:
    result.add cdnkBracket
    # not a weak-dep, since the a complete type is required
    result.add cdnkType, c.requestType(c.env.types.elemType(t)).uint32
    # TODO: pass a valid ConfigRef
    {.cast(noSideEffect).}:
      result.addIntLit c.env.types.length(t).uint64

  of tnkProc:
    case c.env.types.callConv(t)
    of ccClosure:
      result.add cdnkStruct, 2
      result.add cdnkEmpty

      result.addField(c.cache, c.requestFuncType(t), "ClP_0")
      result.addField(c.cache, c.requestType(c.env.types.param(t, ^1)), "ClE_0")

    else:
      result.add cdnkFuncPtr, c.env.types.numParams(t).uint32
      result.addWeakType(c, c.env.types.getReturnType(t))

      for it in c.env.types.params(t):
          # function pointer declarations don't require complete types
          result.addWeakType(c, it)

  of tnkRef, tnkPtr, tnkVar, tnkLent:
    result.add cdnkPtr
    # we only need a weak-dep for the pointer's element type
    result.addWeakType(c, c.env.types.elemType(t))

  of tnkUncheckedArray:
    result.add cdnkBracket
    result.add cdnkType, c.requestType(c.env.types.elemType(t)).uint32
    # ``SEQ_DECL_SIZE`` is a macro defined in ``nimbase.h``
    result.add cdnkIdent, c.cache.getOrIncl("SEQ_DECL_SIZE").uint32

  of tnkCString:
    result.add cdnkPtr
    result.add cdnkIdent, c.cache.getOrIncl("char").uint32

  else:
    let kind = c.env.types[t].kind
    result.add cdnkIdent, c.cache.getOrIncl(fmt"genCType_missing_{kind}").uint32

  assert result.len > 0

func getTypeName(c: var IdentCache, id: TypeId, typ: Type, decl: Declaration): CIdent =
  # TODO: not finished
  if typ.iface != nil:
    assert sfImportc notin typ.iface.flags
    c.getOrIncl(mangledName(typ.iface))
  else:
    # some types require a definition and thus need a name
    case typ.kind
    of tnkProc:
      c.getOrIncl(fmt"proc_{id.uint32}")
    of tnkRecord:
      # a record type without a name is always a tuple
      c.getOrIncl(fmt"tuple_{id.uint32}")
    of tnkArray, tnkUncheckedArray:
      c.getOrIncl(fmt"array_{id.uint32}")
    else:
      # the other types don't need generated names
      InvalidCIdent

const AutoImported = {tnkVoid, tnkBool, tnkChar, tnkInt, tnkUInt, tnkFloat} # types that are treated as imported

func genCTypeInfo(gen: var TypeGenCtx, env: TypeEnv, id: TypeId): CTypeInfo =
  let t = env[id]
  if t.iface != nil and sfImportc in t.iface.flags:
    result = CTypeInfo(name: gen.cache.getOrIncl(mangledName(t.iface)))
  elif t.kind in AutoImported:
    let name =
      case t.kind
      of tnkVoid: "void"
      of tnkChar:  "NIM_CHAR"
      of tnkBool:  "NIM_BOOL"
      of tnkInt:
        {.warning: "NI is never emitted anymore, as we can't detect an `int` here".}
        fmt"NI{t.size}"
      of tnkUInt:  fmt"NU{t.size}"
      of tnkFloat: fmt"NF{t.size}"
      else: unreachable()

    result = CTypeInfo(name: gen.cache.getOrIncl(name))
  else:
    let name = getTypeName(gen.cache, id, t, Declaration())
    var decl = genCTypeDecl(gen, id)

    # set the identifier field for struct and union types:
    if decl[0].kind in {cdnkStruct, cdnkUnion}:
      decl[1] = (cdnkIdent, name.uint32, 0'u32)

    result = CTypeInfo(decl: decl, name: name)


func useFunction(c: var ModuleCtx, s: ProcId) =
  ##
  c.funcs.incl s
  #[
  if lfHeader in s.loc.flags:
    c.headers.incl getStr(s.annex.path)
  elif lfNoDecl notin s.loc.flags:
    discard c.syms.mgetOrPut(s.id, s)
  ]#

func useType(c: var ModuleCtx, t: TypeId) =
  assert t != NoneType
  c.types.incl t

func useTypeAllowNone(c: var ModuleCtx, t: TypeId) =
  # XXX: this shouldn't be allowed, but back-end generated magics have no type
  #      information
  if t != NoneType:
    c.types.incl t

#[
func useTypeWeak(c: var ModuleCtx, t: PType): CTypeId=
  c.types

func useType(c: var ModuleCtx, t: PType): CTypeId =
]#

func requestFunction(c: var GlobalGenCtx, s: SymId): int =
  ## Requests the ID of the C-function `s` maps to
  discard "now a no-op"
  #[
  assert s.kind in routineKinds
  let nextId = c.funcs.len
  result = c.funcMap.mgetOrPut(s.id, nextId)
  if result != nextId:
    assert result < nextId
    # the header's content is generated later; we just reserve the slot here
    c.funcs.setLen(c.funcs.len + 1)
  ]#

func requestTypeName(c: var GlobalGenCtx, t: PType): CIdent =
  # TODO: not finished
  if t.sym != nil:
    c.idents.getOrIncl(mangledName(t.sym))
  else:
    c.idents.getOrIncl(fmt"requestTypeName_missing_{t.kind}")

type GenCtx = object
  f: File
  tmp: int
  sym: ProcId

  names: seq[CAst] # IRIndex -> expr
  types: seq[TypeId]
  config: ConfigRef

  env: #[lent]# ptr IrEnv

  gl: GlobalGenCtx # XXX: temporary
  m: ModuleCtx # XXX: temporary

func gen(c: GenCtx, irs: IrStore3, n: IRIndex): CAst =
  c.names[n]
  #"gen_MISSING"

func mapTypeV3(t: TypeId): CTypeId

func mapTypeV2(c: var GenCtx, t: TypeId): CTypeId =
  # TODO: unfinished
  c.m.useType(t) # mark the type as used
  mapTypeV3(t)

func mapTypeV3(t: TypeId): CTypeId =
  if t != NoneType:
    # XXX: maybe just have a ``NoneType`` -> ``VoidCType`` mapping in the table instead?
    CTypeId(t)
  else:
    VoidCType

func genCProcHeader(idents: var IdentCache, env: ProcedureEnv, s: ProcId): CProcHeader =
  result.ident = idents.getOrIncl(mangledName(env[s].decl))
  result.returnType = mapTypeV3(env.getReturnType(s))

  result.args.newSeq(env.numParams(s))
  var i = 0
  for p in env.params(s):
    result.args[i] = (mapTypeV3(p.typ), idents.getOrIncl(p.name))
    inc i


template start(): CAstBuilder =
  var b: CAstBuilder
  b

func add(c: var CAstBuilder, kind: CAstNodeKind; a, b: uint32 = 0): var CAstBuilder =
  result = c
  c.ast.add (kind, a, b)


func add(x: var CAst, kind: CAstNodeKind; a, b: uint32 = 0) =
  x.add (kind, a, b)

func add(c: var CAstBuilder, other: CAst): var CAstBuilder =
  result = c
  c.ast.add(other)

func emitDeref(c: var CAstBuilder, idents: var IdentCache): var CAstBuilder =
  result = c
  c.ast.add cnkPrefix
  c.ast.add cnkIdent, idents.getOrIncl("*").uint32

func emitAddr(c: var CAstBuilder, idents: var IdentCache): var CAstBuilder =
  result = c
  c.ast.add cnkPrefix
  c.ast.add cnkIdent, idents.getOrIncl("&").uint32

func ident(c: var CAstBuilder, idents: var IdentCache, name: string): var CAstBuilder =
  result = c
  c.ast.add cnkIdent, idents.getOrIncl(name).uint32

func ident(c: var CAstBuilder, ident: CIdent): var CAstBuilder =
  result = c
  c.ast.add cnkIdent, ident.uint32

func intLit(c: var CAstBuilder, v: BiggestInt): var CAstBuilder =
  result = c
  # TODO: int literals need some more development
  c.ast.add cnkIntLit, uint32(cast[uint64](v) shr 32), uint32(cast[uint64](v) and 0xFFFFFFFF'u64)

func strLit(c: var CAstBuilder, strs: var BiTable[string], s: sink string): var CAstBuilder =
  result = c
  c.ast.add cnkStrLit, strs.getOrIncl(s).uint32

func sub(c: var CAstBuilder): var CAstBuilder =
  result = c

func fin(c: sink CAstBuilder): CAst =
  swap(result, c.ast) # XXX: `swap` is used for refc-compatibility

func genError(c: var GenCtx, str: string): CAst =
  # XXX: cnkError always takes a string literal for now
  result.add cnkError, c.gl.strings.getOrIncl(str).uint32

func genArithm(c: var GenCtx, i: IRIndex, check: bool): CAst =
  c.genError("genArithm_missing")

func getTypeArg(irs: IrStore3, arg: IRIndex): TypeId =
  let arg = irs.at(arg)
  case arg.kind
  of ntkLit:
    irs.getLit(arg).typ
  else:
    unreachable(arg.kind)

func genBraced(elems: varargs[CAst]): CAst =
  result.add cnkBraced, elems.len.uint32
  for it in elems.items:
    result.add it

func ident(c: var GlobalGenCtx, name: string): CAst =
  result.add cnkIdent, c.idents.getOrIncl(name).uint32

func genBuiltin(c: var GenCtx, irs: IrStore3, bc: BuiltinCall, n: IrNode3): CAst =
  case bc
  of bcNewClosure:
    genBraced(c.gl.ident("NIM_NIL"), c.gl.ident("NIM_NIL"))
  of bcOverflowCheck:
    genArithm(c, n.args(0), true)
  of bcUnlikely:
    start().add(cnkCall, 1).ident(c.gl.idents, "NIM_UNLIKELY").add(c.gen(irs, n.args(0))).fin()
  of bcCast:
    let dstTyp = n.typ
    var ast = start()
    discard ast.add(cnkCast).add(cnkType, mapTypeV2(c, dstTyp).uint32).add(gen(c, irs, n.args(0)))
    ast.fin()
  of bcRaise:
    var ast = start()
    if argCount(n) == 0:
      # re-raise
      discard ast.add(cnkCall, 0).ident(c.gl.idents, "reraiseException")
    else:
      # TODO: empty arguments
      discard ast.add(cnkCall, 5).ident(c.gl.idents, "raiseExceptionEx")
      discard ast.add(c.gen(irs, n.args(0))).add(c.gen(irs, n.args(1)))
      discard ast.ident(c.gl.idents, "NIM_NIL").ident(c.gl.idents, "NIM_NIL").intLit(0)

    ast.fin()

  else:
    genError(c, fmt"missing: {bc}")
    #unreachable(bc)

type MagicKind = enum
  mkUnary
  mkBinary
  mkCall

func genMagic(c: var GenCtx, irs: IrStore3, m: TMagic, n: IrNode3): CAst =
  let (kind, sym) =
    case m
    of mNot: (mkUnary, "!")
    of mEqRef: (mkBinary, "==")
    else:
      return genError(c, fmt"missing magic: {m}")

  case kind
  of mkUnary:
    # TODO: assert arg count == 1
    result = start().add(cnkPrefix).ident(c.gl.idents, sym).add(gen(c, irs, n.args(0))).fin()
  of mkBinary:
    result = start().add(cnkInfix).add(gen(c, irs, n.args(0))).ident(c.gl.idents, sym).add(gen(c, irs, n.args(1))).fin()
  of mkCall:
    result = genError(c, fmt"missing magic call: {sym}")


func genLit(c: var GenCtx, literal: Literal): CAst =
  let lit = literal.val
  if lit == nil:
    # `nil` as the value is used for type literals
    return start().add(cnkType, mapTypeV2(c, literal.typ).uint32).fin()

  case lit.kind
  of nkIntLit:
    start().intLit(lit.intVal).fin()
  of nkStrLit:
    if lit.typ == nil:
      # XXX: some passes insert string literals without type information. It's supported for now
      # treat as cstring
      start().strLit(c.gl.strings, lit.strVal).fin()
    else:
      case lit.typ.kind
      of tyString, tyDistinct:
        # XXX: the string lit handling is probably too late here and should be
        #      done as part of the `seq` lowering passes instead
        # XXX: this currently only takes the old GC-based strings into account
        if lit.strVal.len == 0:
          # XXX: yeah, this is bad. The lowering needs to happen at the IR level
          start().add(cnkCast).ident(c.gl.idents, "NimStringDesc*").ident(c.gl.idents, "NIM_NIL").fin()
        else:
          genError(c, fmt"missing lit: non-empty tyString")
      of tyCstring:
        start().strLit(c.gl.strings, lit.strVal).fin()
      else:
        unreachable(lit.typ.kind)
  of nkNilLit:
    start().ident(c.gl.idents, "NIM_NIL").fin()
  else:
    genError(c, fmt"missing lit: {lit.kind}")

template testNode(cond: bool, i: IRIndex) =
  if not cond:
    debugEcho astToStr(cond), " failed"
    debugEcho "node: ", i
    printIr(irs, c.env[], exprs)
    for e in irs.traceFor(i).items:
      debugEcho e
    if irs.at(i).kind == ntkLocal:
      debugEcho "trace for local:"
      for e in irs.traceForLocal(irs.getLocalIdx(i)).items:
        debugEcho e
    doAssert false

proc genCode(c: var GenCtx, irs: IrStore3): CAst =
  var i = 0
  template names: untyped = c.names
  template types: untyped = c.types
  template f: untyped = c.f

  var numStmts = 0
  result.add cnkStmtList

  var tmp = 0
  for typ, sym in irs.locals:
    if sym != NoneSymbol:
      discard
      #[
      if lfHeader in sym.loc.flags:
        let str = getStr(sym.annex.path)
        continue
      elif lfNoDecl in sym.loc.flags:
        continue
      ]#

    result.add cnkDef
    result.add cnkType, mapTypeV2(c, typ).uint32
    if sym != NoneSymbol: # TODO: don't test for temps like this
      result.add c.gl.ident mangledName(c.env.syms[sym].decl)

    else:
      result.add c.gl.ident(fmt"_tmp{tmp}")
      inc tmp

    inc numStmts

  let exprs = calcStmt(irs)
  names.newSeq(irs.len)

  for n in irs.nodes:
    case n.kind
    of ntkSym:
      let sId = irs.sym(n)
      let sym = c.env.syms[sId]
      # TODO: refactor
      if sym.kind in {skVar, skLet} and sfGlobal in sym.flags:
        c.m.syms.incl sId
        #discard mapTypeV3(c.gl, sym.typ) # XXX: temporary

      if sym.typ != NoneType:
        useType(c.m, sym.typ)

      names[i] = start().ident(c.gl.idents, mangledName(sym.decl)).fin()
    of ntkProc:
      let prc = c.env.procs[n.procId]
      if prc.magic == mNone:
        useFunction(c.m, n.procId)

      names[i] = start().ident(c.gl.funcs[toIndex(n.procId)].ident).fin()
    of ntkLocal:
      let (kind, typ, sym) = irs.getLocal(i)
      if sym == NoneSymbol:
        names[i] = start().ident(c.gl.idents, "_tmp" & $c.tmp).fin()
        inc c.tmp
      else:
        names[i] = start().ident(c.gl.idents, mangledName(c.env.syms[sym].decl)).fin()

    of ntkCall:
      if n.isBuiltIn:
        let name = genBuiltin(c, irs, n.builtin, n)
        names[i] = name
      else:
        let callee = irs.at(n.callee)
        if callee.kind == ntkProc and (let p = c.env.procs[callee.procId]; p.magic != mNone):
          names[i] = genMagic(c, irs, p.magic, n)
        else:
          var res = start().add(cnkCall, n.argCount.uint32).add(names[n.callee])
          for it in n.args:
            discard res.add names[it]
          names[i] = res.fin()

      # TODO: we're missing a proper way to check whether a call is a statement
      if not exprs[i]:#irs.isStmt(n):
        result.add names[i]
        inc numStmts
    of ntkAddr:
      names[i] = start().emitAddr(c.gl.idents).add(names[n.addrLoc]).fin()
    of ntkDeref:
      names[i] = start().emitDeref(c.gl.idents).add(names[n.addrLoc]).fin()
    of ntkAsgn:
      testNode names[n.srcLoc].len > 0, i
      result.add start().add(cnkInfix).add(names[n.wrLoc]).ident(c.gl.idents, "=").add(names[n.srcLoc]).fin()
      inc numStmts
    of ntkPathObj:
      let
        typId = types[n.srcLoc]
        typ = c.env.types[typId]
        field = c.env.types.field(c.env.types.nthField(typId, n.fieldIdx).toIndex)
      let src = names[n.srcLoc]
      var ast = start().add(cnkDotExpr).add(src)

      # accessing a record means that we need a complete type. While the type
      # we're marking as used here isn't necessarily the type that holds the
      # field we're accessing (i.e. inheritance is used), the base types are
      # automatically also pulled in
      c.m.useType(typId)

      if field.sym != NoneSymbol:
        discard ast.ident(c.gl.idents, mangledName(c.env.syms[field.sym].decl))
      else:
        # TODO: this needs some name clash protection
        discard ast.ident(c.gl.idents, fmt"Field{n.fieldIdx}")

      names[i] = ast.fin()

    of ntkPathArr:
      names[i] = start().add(cnkBracket).add(names[n.srcLoc]).add(names[n.arrIdx]).fin()
    of ntkLit:
      names[i] = genLit(c, irs.getLit(n))
    of ntkUse:
      names[i] = names[n.srcLoc]
    of ntkBranch:
      result.add cnkIf
      result.add names[n.cond]
      result.add cnkStmtList, 1
      result.add cnkGoto, c.gl.idents.getOrIncl(fmt"label{n.target}").uint32
      inc numStmts
    of ntkJoin:
      if irs.isLoop(n.joinPoint):
        result.add genError(c, "loop impl missing")
        discard#f.writeLine "while (true) {"
      else:
        result.add cnkLabel, c.gl.idents.getOrIncl(fmt"label{n.joinPoint}").uint32
      inc numStmts
    of ntkGoto:
      if irs.isLoop(n.target):
        # there exists only one `goto loop` and it's at the end of the loop
        # XXX: very brittle
        result.add genError(c, "loop impl missing")
      else:
        result.add cnkGoto, c.gl.idents.getOrIncl(fmt"label{n.target}").uint32

      inc numStmts
    else:
      names[i] = genError(c, fmt"missing impl: {n.kind}")
      if not exprs[i]:
        result.add names[i]
        inc numStmts

    inc i

  # exit
  # TODO: ``NoneType`` should only mean "no type information", not "void"
  if c.env.procs.getReturnType(c.sym) != NoneType:
    result.add cnkReturn
  else:
    result.add cnkReturn, 1
    result.add cnkIdent, c.gl.idents.getOrIncl("result").uint32
  inc numStmts

  echo numStmts
  result[0].a = numStmts.uint32

proc emitCDecl(f: File, c: GlobalGenCtx, decl: CDecl)

proc emitType(f: File, c: GlobalGenCtx, t: CTypeId) =
  let info {.cursor.} = c.ctypes[t.int]
  if info.name != InvalidCIdent:
    f.write c.idents[info.name]
  else:
    # the declaration is emitted directly if a type has no name
    emitCDecl(f, c, info.decl)

proc emitCAst(f: File, c: GlobalGenCtx, ast: CAst, pos: var int)

proc emitAndEscapeIf(f: File, c: GlobalGenCtx, ast: CAst, pos: var int, notSet: set[CAstNodeKind]) =
  if ast[pos].kind in notSet:
    emitCAst(f, c, ast, pos)
  else:
    f.write "("
    emitCAst(f, c, ast, pos)
    f.write ")"


proc emitCAst(f: File, c: GlobalGenCtx, ast: CAst, pos: var int) =
  if pos >= ast.len:
    for it in ast:
      echo it

  let n = ast[pos]
  inc pos

  case n.kind
  of cnkError:
    f.write "GEN_ERROR(\""
    f.write c.strings[n.a.LitId]
    f.write "\")"
  of cnkStmtList:
    for _ in 0..<n.a:
      emitCAst(f, c, ast, pos)
      f.writeLine ";"

  of cnkDef:
    emitCAst(f, c, ast, pos) # type
    f.write " "
    emitCAst(f, c, ast, pos) # ident
    if n.a != 0'u32:
      f.write " = "
      emitCAst(f, c, ast, pos) # initializer
    else:
      f.write ";"

  of cnkIdent:
    f.write c.idents[n.a.LitId]

  of cnkInfix:
    emitCAst(f, c, ast, pos) # lhs
    f.write " "
    emitCAst(f, c, ast, pos) # infix
    f.write " "
    emitCAst(f, c, ast, pos) # rhs

  of cnkPrefix:
    emitCAst(f, c, ast, pos)
    f.write "("
    emitCAst(f, c, ast, pos)
    f.write ")"

  of cnkBracket:
    emitAndEscapeIf(f, c, ast, pos, {cnkIdent})
    f.write "["
    emitCAst(f, c, ast, pos)
    f.write "]"

  of cnkCall:
    emitAndEscapeIf(f, c, ast, pos, {cnkIdent}) # callee
    f.write "("
    for i in 0..<n.a:
      if i > 0:
        f.write ", "

      emitCAst(f, c, ast, pos)

    f.write ")"

  of cnkIf:
    f.write "if ("
    emitCAst(f, c, ast, pos) # condition
    f.writeLine ") {"
    emitCAst(f, c, ast, pos) # stmt list
    f.write "}"

  of cnkReturn:
    f.write "return"
    if n.a == 1:
      emitCAst(f, c, ast, pos)

  of cnkLabel:
    f.write c.idents[n.a.LitId]
    f.writeLine ":"
  of cnkGoto:
    f.write "goto "
    f.write c.idents[n.a.LitId]
  of cnkDotExpr:
    f.write "("
    emitCAst(f, c, ast, pos)
    f.write ")."
    emitCAst(f, c, ast, pos)

  of cnkStrLit:
    f.write '"'
    f.write c.strings[n.a.LitId]
    f.write '"'

  of cnkIntLit:
    f.write (n.a.uint64 shl 64) or n.b.uint64

  of cnkType:
    emitType(f, c, n.a.CTypeId)

  of cnkCast:
    f.write "("
    emitCAst(f, c, ast, pos)
    f.write ") ("
    emitCAst(f, c, ast, pos)
    f.write ")"

  of cnkBraced:
    f.write "{"
    for i in 0..<n.a:
      if i > 0:
        f.write ", "
      emitCAst(f, c, ast, pos)
    f.write "}"

  else:
    f.write "EMIT_ERROR(\"missing " & $n.kind & "\")"

proc emitCAst(f: File, c: GlobalGenCtx, ast: CAst) =
  var pos = 0
  while pos < ast.len:
    emitCAst(f, c, ast, pos)


proc emitCDecl(f: File, c: GlobalGenCtx, decl: CDecl, pos: var int)

proc emitFuncDecl(f: File, c: GlobalGenCtx, decl: CDecl, ident: CIdent, L: int, pos: var int) =
  emitCDecl(f, c, decl, pos) # return type
  if ident != InvalidCIdent:
    f.write "(*"
    f.write c.idents[ident]
    f.write ")("
  else:
    f.write "(*)("
  for i in 0..<L:
    if i > 0:
      f.write ", "

    emitCDecl(f, c, decl, pos)

  f.write ")"

proc emitCDecl(f: File, c: GlobalGenCtx, decl: CDecl, pos: var int) =
  if pos >= decl.len:
    for it in decl:
      echo it
  let n = decl[pos]
  inc pos

  case n.kind
  of cdnkStruct, cdnkUnion:
    f.write:
      if n.kind == cdnkStruct: "struct "
      else: "union "

    emitCDecl(f, c, decl, pos)
    f.writeLine "{"
    for _ in 0..<n.a:
      emitCDecl(f, c, decl, pos)
      f.writeLine ";"

    f.write "}"

  of cdnkField:
    emitCDecl(f, c, decl, pos) # type
    f.write " "
    emitCDecl(f, c, decl, pos) # name

  of cdnkType:
    let info {.cursor.} = c.ctypes[n.a.uint32]
    if info.name == InvalidCIdent:
      emitCDecl(f, c, info.decl)
    else:
      f.write c.idents[info.name]

  of cdnkWeakType:
    let info {.cursor.} = c.ctypes[n.a.uint32]
    assert info.name != InvalidCIdent

    f.write c.idents[info.name]

  of cdnkPtr:
    emitCDecl(f, c, decl, pos)
    f.write "*"

  of cdnkIdent:
    f.write c.idents[n.a.CIdent]

  of cdnkIntLit:
    let val = n.a.uint64 or (n.b.uint64 shl 32)
    f.write $val

  of cdnkBracket:
    emitCDecl(f, c, decl, pos)
    f.write "["
    emitCDecl(f, c, decl, pos)
    f.write "]"

  of cdnkFuncPtr:
    emitFuncDecl(f, c, decl, InvalidCIdent, n.a.int, pos)

  of cdnkEmpty:
    discard "nothing"


proc emitCDecl(f: File, c: GlobalGenCtx, decl: CDecl) =
  var pos = 0
  emitCDecl(f, c, decl, pos)

proc emitCType(f: File, c: GlobalGenCtx, info: CTypeInfo, isFwd: bool) =
  var pos = 0

  assert info.decl.len > 0, c.idents[info.name]

  let kind = info.decl[0].kind
  case kind
  of cdnkStruct, cdnkUnion:
    if isFwd:
      # --> ``typdef struct X X;``
      # forward-declare the record type and make the identifier available in
      # the ordinary namespace
      f.write "typedef "
      f.write:
        case kind
        of cdnkStruct: "struct"
        of cdnkUnion:  "union"
        else: unreachable()

      f.write fmt" {c.idents[info.name]}"
      f.write fmt" {c.idents[info.name]}"
      pos = info.decl.len # mark the body as processed
    else:
      # definition requested
      emitCDecl(f, c, info.decl, pos)

  of cdnkBracket:
    f.write "typedef "
    pos = 1
    emitCDecl(f, c, info.decl, pos)
    f.write " "
    f.write c.idents[info.name]
    f.write "["
    emitCDecl(f, c, info.decl, pos) # the array size
    f.write "]"
  of cdnkFuncPtr:
    f.write "typedef "
    pos = 1
    emitFuncDecl(f, c, info.decl, info.name, info.decl[0].a.int, pos)
  else:
    f.write "typedef "
    emitCDecl(f, c, info.decl, pos)
    f.write " "
    f.write c.idents[info.name]

  f.writeLine ";"

  assert pos == info.decl.len

proc writeDecl(f: File, c: GlobalGenCtx, h: CProcHeader, decl: Declaration) =
  emitType(f, c, h.returnType)
  f.write(" ")
  f.write(c.idents[h.ident])
  f.write("(")
  for i, it in h.args.pairs:
    if i > 0:
      f.write ", "

    emitType(f, c, it.typ)

  f.writeLine(");")

proc writeDef(f: File, c: GlobalGenCtx, h: CProcHeader, decl: Declaration) =
  emitType(f, c, h.returnType)
  f.write(" ")
  f.write(c.idents[h.ident])
  f.write("(")
  for i, it in h.args.pairs:
    if i > 0:
      f.write ", "

    emitType(f, c, it.typ)
    f.write " "
    f.write c.idents[it.name]

  f.writeLine(") {")

func initGlobalContext*(c: var GlobalGenCtx, env: IrEnv) =
  ## Initializes the ``GlobalGenCtx`` to use for all following ``emitModuleToFile`` calls. Creates the ``CTypeInfo`` for each IR type.

  var gen = TypeGenCtx(weakTypes: {tnkRecord}, env: unsafeAddr env)
  swap(gen.cache, c.idents)

  # XXX: a leftover from the CTypeId -> TypeId transition. Needs to be removed
  c.ctypes.add(CTypeInfo(name: gen.cache.getOrIncl("void"))) # the `VoidCType`

  # TODO: use ``setLen`` + []
  for id in types(env.types):
    c.ctypes.add genCTypeInfo(gen, env.types, id)

  swap(gen.cache, c.idents)

  # create the procedure headers
  # TODO: use ``setLen`` + []
  for id in env.procs.items:
    c.funcs.add genCProcHeader(c.idents, env.procs, id)

proc emitModuleToFile*(conf: ConfigRef, filename: AbsoluteFile, ctx: var GlobalGenCtx, env: IrEnv, procs: openArray[(ProcId, IrStore3)]) =
  let f = open(filename.string, fmWrite)
  defer: f.close()

  echo "Here: ", filename.string

  var
    mCtx: ModuleCtx
    asts: seq[CAst]

  mCtx.headers.incl("\"nimbase.h\"")

  for sym, irs in procs.items:
    useFunction(mCtx, sym)

    if sfImportc in env.procs[sym].flags:
      asts.add(default(CAst))
      continue

    echo "genFor: ", env.procs[sym].decl.name #, " at ", conf.toFileLineCol(sym.info)
    var c = GenCtx(f: f, config: conf, sym: sym, env: unsafeAddr env)
    # doing a separate pass for the type computation instead of doing it in
    # `genCode` is probably a bit less efficient, but it's also simpler;
    # requires less code duplication; and is also good for modularity
    c.types = computeTypes(irs, env)

    swap(c.gl, ctx)
    swap(c.m, mCtx)
    asts.add genCode(c, irs)
    swap(c.m, mCtx)
    swap(c.gl, ctx)

  # XXX: this might lead to an ordering problem, since we're not registering
  #      the types on the first occurence
  # mark the types used in routine signatures as used
  for id in mCtx.funcs.items:
    mCtx.useTypeAllowNone(env.procs.getReturnType(id))

    for it in env.procs.params(id):
      mCtx.useType(it.typ)

  # mark the type of used non-proc symbols as used
  for id in mCtx.syms.items:
    mCtx.useType(env.syms[id].typ)

  # collect all types that we need to be defined in this translation unit (.c file)

  type TypeDef = tuple[fwd: bool, id: CTypeId]

  func collectFwd(list: var seq[TypeDef], types: seq[CTypeInfo], id: CTypeId, marker, markerFwd: var PackedSet[CTypeId]) =
    if id notin marker and not markerFwd.containsOrIncl(id):
      # not defined nor forward declared
      assert types[id.int].name != InvalidCIdent
      list.add (true, id)

  func collectOrdered(list: var seq[TypeDef], types: seq[CTypeInfo],
                      id: CTypeId, marker, markerFwd: var PackedSet[CTypeId]) =
    let info {.cursor.} = types[id.int]
    if marker.containsOrIncl(id):
      # nothing to do
      return

    # scan the type's body for dependencies and add them first
    for n in info.decl.items:
      case n.kind
      of cdnkType:
        # requires a definition
        collectOrdered(list, types, n.a.CTypeId, marker, markerFwd)
      of cdnkWeakType:
        # only requires a forward declaration
        collectFwd(list, types, n.a.CTypeId, marker, markerFwd)
      else:
        discard

    # XXX: the used headers could also be collected here, but that would grow
    # the required state even more

    if info.name != InvalidCIdent:
      # only collect types that have an identifier. The others don't need a
      # typedef (they're inlined directly) and also don't/can't have header
      # dependency information attached
      list.add (false, id)

  var typedefs: seq[TypeDef]
  var marker, markerFwd: PackedSet[CTypeId]
  for it in mCtx.types.items:
    collectOrdered(typedefs, ctx.ctypes, it, marker, markerFwd)

  marker.reset() # no longer needed

  # collect the header dependencies from the used types
  # XXX: to be more efficient, writing out the header includes for the types
  #      could be combined with emitting the type definitions

  for _, id in typedefs.items:
    let iface = env.types[id].iface
    if iface != nil and lfHeader in iface.loc.flags:
      echo ctx.idents[ctx.ctypes[id.int].name], ": ", iface.loc.flags
      mCtx.headers.incl getStr(iface.annex.path)

  # ----- start of the emit logic -----

  f.writeLine "#define NIM_INTBITS 64" # TODO: don't hardcode

  # headers
  for h in mCtx.headers.items:
    f.writeLine fmt"#include {h}"

  # type section

  for fwd, id in typedefs.items:
    let info = ctx.ctypes[id.int]
    # imported types don't have a body
    if info.decl.len > 0:
      if not fwd and info.decl[0].kind in {cdnkStruct, cdnkUnion} and id notin markerFwd:
        # struct and unions types always use a forward-declaration bacause the
        # emitted typedef makes the identifier available in the ordinary
        # name-space
        emitCType(f, ctx, ctx.ctypes[id.int], isFwd=true)

      emitCType(f, ctx, ctx.ctypes[id.int], isFwd=fwd)

  # generate all procedure forward declarations
  for id in mCtx.funcs.items:
    #echo "decl: ", sym.name.s, " at ", conf.toFileLineCol(sym.info)
    writeDecl(f, ctx, ctx.funcs[id.toIndex], env.procs[id].decl)

  for id in mCtx.syms.items:
    let sym = env.syms[id]
    case sym.kind
    of skLet, skVar:
      emitType(f, ctx, sym.typ)
      f.write " "
      f.write mangledName(sym.decl)
      f.writeLine ";"
    of skConst:
      f.writeLine "EMIT_ERROR(\"missing logic: const\")"
    else:
      unreachable(sym.kind)

  var i = 0
  for it in asts.items:
    if it.len == 0:
      inc i
      continue

    let
      (id, _) = procs[i]
      prc = env.procs[id]

    writeDef(f, ctx, ctx.funcs[id.toIndex], prc.decl)
    try:
      emitCAst(f, ctx, it)
    except:
      echo "emit: ", prc.decl.name#, " at ", conf.toFileLineCol(sym.info)
      raise
    f.writeLine "}"
    inc i