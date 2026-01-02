## Implements the LLVM code generator. The code generator takes CGIR modules as
## input and produces LLVM assembler modules, nothing else.
##
## Only a subset of the CGIR is supported:
## * no support for exception handling
## * no support for strings-as-locations (C-like string literals)

# the code is a heavily-modified version of the C code generator, but be
# warned that code quality is abhorrent

import
  std/[
    math, # for float classification
    packedsets,
    strutils,
    strformat,
    tables
  ],
  std/private/[
    containers
  ],
  compiler/backend/[
    cgir2
  ],
  compiler/ic/[
    bitabs
  ]

import system/formatfloat # for float rendering

from compiler/backend/cgen import Emit
export cgen.Emit

type
  Writer = object
    nextLabel: int
    nextTemp: int

    nextMetadata: int
      ## next free name for a metadata item
    metadata: string
      ## code defining the named metadata

    output: string
    currLine: uint16
    currFile: StringId
    anon: Table[Datum, uint32]
      ## datum -> zero-based name suffix
    labels: Table[uint32, string]

    locTable: Table[uint32, uint32]
      ## source location ID -> corresponding LLVM metadata name (which is a number)

  LLVMTypeKind = enum
    tkVoid
    tkPtr
    tkInt
    tkFloat
    tkDouble
    tkOpaque
    tkFunc
    tkAggregate # not a real type

  LLVMType = object
    case kind: LLVMTypeKind
    of tkVoid, tkPtr, tkFloat, tkDouble, tkOpaque, tkFunc: discard
    of tkInt: width: int
    of tkAggregate: name: string

  PrimitiveType = object
    case kind: CgNodeKind
    of cnkUIntTy, cnkIntTy, cnkFloatTy:
      width: int
    of cnkPtrTy:
      discard
    of cnkOpaqueTy:
      name: StringId
    else:
      discard

  Value = object
    ind: bool
    typ: LLVMType
    val: string

using
  m: CgModule
  ast: Ast
  pos: var NodeIndex

const
  CallingConvToStr = [
    Default: "ccc",
    Nimcall: "fastcc",  Stdcall:  "cc 64",
    Cdecl:   "ccc",     Safecall: "cc 64",
    Syscall: "ccc",     Fastcall: "cc 65"
  ]
  PreferIdentified = {cnkStructTy, cnkUnionTy}
    ## types that must not be inlined where a name exists

proc intType(width: Positive): LLVMType =
  LLVMType(kind: tkInt, width: width)

proc newTemp(c: var Writer): string =
  result = "%" & $c.nextTemp
  inc c.nextTemp

proc newLabel(c: var Writer): string =
  result = "L" & $c.nextLabel
  inc c.nextLabel

proc makeVal(typ: sink LLVMType, val: sink string): Value =
  Value(ind: false, typ: typ, val: val)

proc makeIndirect(typ: sink LLVMType, val: sink string): Value =
  Value(ind: true, typ: typ, val: val)

proc pushLabel(c: var Writer, lab: uint32): string =
  result = c.newLabel()
  c.labels[lab] = result

proc advance(ast, pos): CgNode {.inline.} =
  result = ast[pos]
  inc pos

proc skip(ast, pos) {.inline.} =
  pos = ast.next(pos)

proc toSet[T](m; val: uint32, _: typedesc[T]): set[T] =
  cast[set[T]](m.unpackUInt(val))

proc len(n: CgNode): int =
  n.val.int

proc readInt(m; ast, pos): int64 =
  m.unpackInt(advance(ast, pos).val)
proc readUInt(m; ast, pos): uint64 =
  m.unpackUInt(advance(ast, pos).val)
proc readSet[T](m; ast; pos; _: typedesc[T]): set[T] =
  m.toSet(advance(ast, pos).val, T)

proc resolve(m: CgModule, n: NodeIndex): NodeIndex =
  if m.tast[n].kind == cnkType:
    m.types[m.tast[n].val.StringId]
  else:
    n

proc getType(m; pos: NodeIndex): NodeIndex =
  ## Returns the index of the type AST representing the result type of the
  ## expression at `n`.
  case m.ast[pos].kind
  of cnkExprs - {cnkCall, cnkNilLit}:
    m.types[m.ast[pos, 0].val.StringId]
  of cnkCall, cnkTailCall:
    # fetch the return type of the callee's proc type
    var callee = getType(m, m.ast.child(pos, 0))
    if m.tast[callee].kind == cnkPtrTy:
      callee = resolve(m, m.tast.child(callee, 0))
    m.tast.child(callee, 1)
  else:
    unreachable(m.ast[pos].kind)

proc add(r: var Writer, str: string) =
  r.output.add str
proc addInt(r: var Writer, i: int64) =
  r.output.addInt i

proc addChar(r: var string, c: char) =
  ## Emits character value `c`, using a C escape sequence where required.
  case c
  of '\0'..'\x1F', '\x7F'..'\xFF':
    r.add '\\'
    const chars = "0123456789abcdef"
    r.add chars[ord(c) div 16]
    r.add chars[ord(c) and 15]
  of '\"':
    r.add "\\22"
  of '\\':
    r.add "\\\\"
  else:
    r.add c

proc align(val: int64, to: int64): int64 =
  let mask = to - 1
  (val + mask) and not mask

proc formatValue(r: var string, val: LLVMType, prec: string) =
  case val.kind
  of tkVoid:
    r.add "void"
  of tkPtr:
    r.add "ptr"
  of tkInt:
    r.add "i"
    r.addInt val.width
  of tkFloat:
    r.add "float"
  of tkDouble:
    r.add "double"
  of tkOpaque:
    r.add "opaque"
  of tkAggregate:
    r.add val.name
  of tkFunc:
    unreachable()

proc formatValue(r: var string, val: Value, prec: string) =
  r.formatValue(val.typ, "")
  r.add " "
  r.add val.val

type
  SizeAlignState = object
    ## Accumulator object for size/alignment computation.
    size: int64
    alignment: int16

proc initSizeAlign(): SizeAlignState =
  SizeAlignState(size: 0, alignment: 1)

proc computeSizeAlign(m; pos: NodeIndex): (int64, int16)

proc add(s: var SizeAlignState, size: int64, alignment: int16): int64 =
  let prev = s.size
  s.size = align(s.size, alignment) # add necessary padding
  result = s.size - prev
  s.alignment = max(s.alignment, alignment)
  s.size += size

proc addField(s: var SizeAlignState, m; pos: NodeIndex): int64 =
  ## Updates the size and alignment to include the given field, returning the
  ## padding between it and the previous field.
  let (size, alignment) = computeSizeAlign(m, m.tast.child(pos, 0))
  var fixed = m.unpackInt(m.tast[pos, 1].val).int16
  if fixed == 0:
    fixed = alignment
  s.add(size, fixed)

proc mergeField(s: var SizeAlignState, m; pos: NodeIndex) =
  ## Updates the size and alignment to include the given field in a union.
  let (size, alignment) = computeSizeAlign(m, m.tast.child(pos, 0))
  var fixed = m.unpackInt(m.tast[pos, 1].val).int16
  if fixed == 0:
    fixed = alignment
  s.size = max(s.size, size)
  s.alignment = max(s.alignment, fixed)

proc finish(s: sink SizeAlignState): (int64, int16) =
  # pad the size so that its a multiple of the alignment
  (align(s.size, s.alignment), s.alignment)

proc toPrimitive(m; pos: NodeIndex): PrimitiveType

iterator items(ast: Ast, pos: NodeIndex, start: int): NodeIndex =
  var p = ast.child(pos, start)
  for _ in start..<ast.len(pos):
    yield p
    p = ast.next(p)

proc computeSizeAlign(m; pos: NodeIndex): (int64, int16) =
  ## Computes the size and alignment (both in bytes) of the type at `pos`.
  case m.tast[pos].kind
  of cnkType:
    computeSizeAlign(m, m.types[m.tast[pos].val.StringId])
  of cnkCharTy, cnkBoolTy:
    (1'i64, 1'i16)
  of cnkIntTy, cnkUIntTy, cnkFloatTy:
    let size = m.unpackInt(m.tast[pos, 0].val)
    (size, int16(size))
  of cnkPtrTy:
    # TODO: use target's pointer size
    (8'i64, 8'i16)
  of cnkStructTy:
    var s = initSizeAlign()
    for it in items(m.tast, pos, 1):
      discard s.addField(m, it)
    s.finish()
  of cnkUnionTy:
    var s = initSizeAlign()
    for it in items(m.tast, pos, 1):
      s.mergeField(m, it)
    s.finish()
  of cnkArrayTy:
    let (size, align) = computeSizeAlign(m, m.tast.child(pos, 1))
    (size * m.unpackInt(m.tast[pos, 0].val), align)
  of cnkOpaqueTy:
    let n = toPrimitive(m, pos)
    case n.kind
    of cnkPtrTy:
      (8'i64, 8'i16)
    of cnkIntTy, cnkUIntTy, cnkFloatTy:
      (n.width.int64 div 8, n.width.int16 div 8)
    else:
      unreachable()
  else:
    unreachable(m.tast[pos].kind)

proc newMetadata(r: var Writer, expr: string): string =
  r.metadata.add &"!{r.nextMetadata} = {expr}\n"
  # XXX: use a distinct type and render the name when during string
  #      interpolation...
  result = "!" & $r.nextMetadata

# proc getSourceLoc(r: var Writer, info: TLineInfo): string =

proc typeToC(m; pos; r: var Writer): LLVMType

proc structToLLVM(m; pos; r: var Writer): string =
  ## Translates a struct/union type.
  let n = advance(m.tast, pos)
  let packed = readInt(m, m.tast, pos) == 1
  # TODO: implement packing
  if n.kind == cnkStructTy:
    result.add "{"
    var offset = 0'i64
    for i in 1..<len(n):
      if i > 1:
        result.add ", "
      discard advance(m.tast, pos)
      var tpos = pos
      skip(m.tast, pos)
      let align = readInt(m, m.tast, pos)
      let attribs = readSet(m, m.tast, pos, CgLocAttrib)
      let bitsize = readInt(m, m.tast, pos)
      # ignore the bitsize modifier. LLVM supports arbitrary integer bit
      # widths, but the bitsize modifier is a C-ism that shouldn't exist in
      # the first place, so don't bother
      skip(m.tast, pos) # ignore the name
      result.formatValue(typeToC(m, tpos, r), "")
    result.add "}"
  else:
    # there are no union types in LLVM. They're represented via an aggregate
    # type whose size and alignment matches that of the union
    var s = initSizeAlign()
    for i in 1..<len(n):
      s.mergeField(m, pos)
      skip(m.tast, pos)

    # TODO: handle over-alignment correctly
    let (size, align) = s.finish()
    if size == align:
      result.add fmt"i{size * 8}"
    else:
      # embed the most-aligned type so that the union's alignment is correct
      assert size > align
      result.add "{ i$1, [$2 x i8] }" % [$(align * 8), $(size - align)]

proc typeRefToC(m; typ: StringId, r: var Writer): LLVMType

const
  BoolType = intType(1)
  CgBoolType = intType(8)
  CharType = intType(8)
  PtrType = LLVMType(kind: tkPtr)
  VoidType = LLVMType(kind: tkVoid)

proc toPrimitive(m; pos: NodeIndex): PrimitiveType =
  case m.tast[pos].kind
  of cnkIntTy, cnkUIntTy, cnkFloatTy:
    var typ = PrimitiveType(kind: m.tast[pos].kind)
    typ.width = int(m.unpackInt(m.tast[pos, 0].val) * 8)
    typ
  of cnkPtrTy:
    PrimitiveType(kind: m.tast[pos].kind)
  of cnkBoolTy:
    PrimitiveType(kind: cnkUIntTy, width: 8)
  of cnkCharTy:
    PrimitiveType(kind: cnkUIntTy, width: 8)
  of cnkOpaqueTy:
    case m.get(m.tast[pos, 0].val.StringId)
    of "size_t":
      # TODO: use the target's pointer size
      PrimitiveType(kind: cnkUIntTy, width: 64)
    of "unsigned long long":
      PrimitiveType(kind: cnkUIntTy, width: 64)
    of "long long":
      PrimitiveType(kind: cnkIntTy, width: 64)
    of "unsigned long", "unsigned int":
      PrimitiveType(kind: cnkUIntTy, width: 32)
    of "long", "int":
      PrimitiveType(kind: cnkIntTy, width: 32)
    of "unsigned short":
      PrimitiveType(kind: cnkUIntTy, width: 16)
    of "short":
      PrimitiveType(kind: cnkIntTy, width: 16)
    of "unsigned char":
      PrimitiveType(kind: cnkUIntTy, width: 8)
    of "char":
      PrimitiveType(kind: cnkIntTy, width: 8)
    of "double":
      PrimitiveType(kind: cnkFloatTy, width: 64)
    of "float":
      PrimitiveType(kind: cnkFloatTy, width: 32)
    of "uintptr_t", "intptr_t":
      # TODO: use the target's pointer size
      PrimitiveType(kind: cnkPtrTy)
    # Windows-specific types
    of "HINSTANCE", "HMODULE", "FARPROC":
      PrimitiveType(kind: cnkPtrTy)
    of "clock_t":
      # a long
      PrimitiveType(kind: cnkIntTy, width: 32) # XXX: not cross-platform safe
    of "time_t":
      PrimitiveType(kind: cnkIntTy, width: 64) # XXX: not cross-platform safe
    else:
      echo "opaque: ", m.get(m.tast[pos, 0].val.StringId)
      PrimitiveType(kind: cnkOpaqueTy, name: m.tast[pos, 0].val.StringId)
  else:
    unreachable()

proc toLLVM(typ: PrimitiveType): LLVMType =
  case typ.kind
  of cnkIntTy, cnkUIntTy: intType(typ.width)
  of cnkPtrTy: PtrType
  of cnkFloatTy:
    case typ.width
    of 32: LLVMType(kind: tkFloat)
    of 64: LLVMType(kind: tkDouble)
    else:  unreachable()
  of cnkOpaqueTy:
    LLVMType(kind: tkOpaque)
  else:    unreachable()

proc formatValue(r: var string, val: PrimitiveType, prec: string) =
  r.formatValue(toLLVM(val), "")

proc typeToC(m; pos; r: var Writer): LLVMType =
  ## Emits the body for a type.
  let n = advance(m.tast, pos)
  case n.kind
  of cnkStructTy, cnkUnionTy:
    # an anonymous inline struct/union
    dec pos # go back to the header
    LLVMType(kind: tkAggregate, name: structToLLVM(m, pos, r))
  of cnkArrayTy:
    let res = fmt"[{readInt(m, m.tast, pos)} x {typeToC(m, pos, r)}]"
    LLVMType(kind: tkAggregate, name: res)
  of cnkVoidTy:
    LLVMType(kind: tkVoid)
  of cnkBoolTy:
    intType(8)
  of cnkCharTy:
    intType(8)
  of cnkIntTy, cnkUIntTy:
    # LLVM has only signless integers
    intType(readInt(m, m.tast, pos) * 8)
  of cnkFloatTy:
    case readInt(m, m.tast, pos)
    of 4: LLVMType(kind: tkFloat)
    of 8: LLVMType(kind: tkDouble)
    else: unreachable()
  of cnkType:
    typeRefToC(m, n.val.StringId, r)
  of cnkPtrTy:
    skip(m.tast, pos)
    PtrType
  of cnkOpaqueTy:
    dec pos
    let prim = toPrimitive(m, pos)
    skip(m.tast, pos)
    toLLVM(prim)
  else:
    unreachable(n.kind)

proc typeRefToC(m; typ: StringId, r: var Writer): LLVMType =
  ## Emits the C code for a type reference.
  case m.tast[m.types[typ]].kind
  of PreferIdentified:
    LLVMType(kind: tkAggregate, name: "%T." & m.get(typ))
  of cnkProcTy:
    LLVMType(kind: tkFunc)
  else:
    # inline the type expression
    var pos = m.types[typ]
    typeToC(m, pos, r)

proc typeRefToC(m; pos; r: var Writer): LLVMType =
  let n = advance(m.ast, pos)
  assert n.kind == cnkType
  typeRefToC(m, n.val.StringId, r)

proc exprToC(m; pos; r: var Writer): Value

proc add(r: var string, val: Value) =
  r.formatValue(val.typ, "")
  r.add " "
  r.add val.val

proc add(r: var string, val: LLVMType) =
  r.formatValue(val, "")

proc add(r: var Writer, val: LLVMType) =
  r.output.add val

proc add(r: var Writer, val: Value) =
  r.output.add val

proc load(val: sink Value, r: var Writer): Value =
  if val.ind:
    let tmp = r.newTemp()
    r.add &"{tmp} = load {val.typ}, ptr {val.val}\n"
    makeVal val.typ, tmp
  else:
    val

proc expectStorable(val: sink Value, r: var Writer): Value =
  if val.typ.kind == tkInt and val.typ.width < 8:
    # turn an i1 into an i8
    let tmp = r.newTemp()
    r.add &"{tmp} = zext {val} to i8\n"
    makeVal CgBoolType, tmp
  else:
    val

proc exprToReg(m; pos; r: var Writer): Value =
  ## Translates a CGIR expression to LLVM, returning a value with the result.
  ## Were possible, a register holding a storable value (e.g., no i1) is returned.
  result = exprToC(m, pos, r)
  if result.typ.kind == tkAggregate:
    if result.ind:
      # remove the indirection, yielding a "real" address
      result = makeVal(PtrType, result.val)
  else:
    result = expectStorable(load(result, r), r)

proc binOpToC(m; pos; op: string, r: var Writer): Value =
  let typ = typeRefToC(m, pos, r)
  let a = exprToReg(m, pos, r)
  let b = exprToReg(m, pos, r)
  let tmp = r.newTemp()
  r.add &"{tmp} = {op} {a}, {b.val}\n"
  makeVal typ, tmp

proc primTypeRefToC(m; pos; r: var Writer): PrimitiveType =
  toPrimitive(m, m.types[advance(m.ast, pos).val.StringId])

proc fitTo(val: sink Value, to: LLVMType, r: var Writer): Value =
  # FIXME: some incorrectly typed CGIR currently reaches into the code
  #        generators, which we have to work around here. Fix the root cause
  #        and then remove this logic
  if val.typ.kind == tkInt:
    assert to.kind == tkInt
    if val.typ.width < to.width:
      # let us hope zero extension is always correct...
      let tmp = r.newTemp()
      r.add &"{tmp} = zext {val} to {to}\n"
      makeVal to, tmp
    elif val.typ.width > to.width:
      let tmp = r.newTemp()
      r.add &"{tmp} = trunc {val} to {to}\n"
      makeVal to, tmp
    else:
      val
  else:
    val

proc binOpToC(m; pos; iop, uop, fop: string, r: var Writer): Value =
  let typ = primTypeRefToC(m, pos, r)
  let target = toLLVM(typ)
  let a = fitTo(exprToReg(m, pos, r), target, r)
  let b = fitTo(exprToReg(m, pos, r), target, r)
  let tmp = r.newTemp()
  case typ.kind
  of cnkIntTy:
    r.add &"{tmp} = {iop} {a}, {b.val}\n"
  of cnkUIntTy:
    r.add &"{tmp} = {uop} {a}, {b.val}\n"
  of cnkFloatTy:
    r.add &"{tmp} = {fop} {a}, {b.val}\n"
  else:
    unreachable()
  makeVal target, tmp

proc indexToC(m; pos; r: var Writer): Value =
  ## Emits the C code for an index operand.
  if m.ast[pos].kind == cnkInt:
    makeVal intType(32), $readInt(m, m.ast, pos)
  else:
    exprToReg(m, pos, r)

proc pathToC(m; pos; count: int, r: var Writer): Value =
  ## Emits a C access sequence with `count` operands starting at `pos`, for
  ## the type whose description is at `tn`
  let typ = typeRefToC(m, pos, r)
  var tn = getType(m, pos)

  var inp = exprToC(m, pos, r)

  if m.tast[tn].kind == cnkPtrTy:
    assert inp.typ.kind == tkPtr
    tn = resolve(m, m.tast.child(tn, 0))
    inp = load(inp, r)

  var tn2 = tn
  var temp = &"{typeToC(m, tn2, r)}, ptr {inp.val}, i32 0"

  # the meaning of the index value depends on the corresponding type
  for _ in 0..<count:
    case m.tast[tn].kind
    of cnkStructTy:
      let idx = readInt(m, m.ast, pos)
      tn = m.tast.child(tn, 1 + idx)
      temp.add ", i32 "
      temp.addInt idx
      tn = m.tast.child(tn, 0)
    of cnkUnionTy:
      # unions are represented as byte arrays when embedded in aggregate
      # types. Take the address of the union and cast it to the correct type
      let idx = readInt(m, m.ast, pos)
      tn = m.tast.child(m.tast.child(tn, 1 + idx), 0)

      let tmp = r.newTemp()
      r.add &"{tmp} = getelementptr {temp}\n"
      var tpos = tn
      temp = &"{typeToC(m, tpos, r)}, ptr {tmp}, i32 0"
    of cnkOpaqueTy:
      unreachable("unsupported opaque access: " & m.get(m.tast[tn, 0].val.StringId))
    of cnkArrayTy:
      temp.add ", "
      temp.add indexToC(m, pos, r)
      tn = m.tast.child(tn, 1)
    else:
      unreachable(m.tast[tn].kind)
    tn = resolve(m, tn)

  let res = r.newTemp()
  r.add &"{res} = getelementptr {temp}\n"
  makeIndirect typ, res

proc valueToC(m; pos; r: var Writer): Value =
  ## Emits the C code for a `cnkValue` tree. `pos` is expected to point to
  ## the first child node.
  let typ = advance(m.ast, pos).val.StringId
  let tn = m.types[typ]
  let v = advance(m.ast, pos)
  case m.tast[tn].kind
  of cnkBoolTy:
    if v.val == 0:
      makeVal BoolType, "false"
    else:
      makeVal BoolType, "true"
  of cnkCharTy:
    makeVal CharType, $m.unpackUInt(v.val)
  of cnkIntTy, cnkUIntTy:
    # LLVM assembler has no unsigned integer values
    makeVal typeRefToC(m, typ, r), $m.unpackInt(v.val)
  of cnkFloatTy:
    let typ = typeRefToC(m, typ, r)
    let f = m.unpackFloat(v.val)
    case classify(f)
    of fcNan:
      makeVal typ, "0x" & toHex(cast[uint64](f))
    of fcZero:
      makeVal typ, "0.0"
    of fcNegZero:
      makeVal typ, "-0.0"
    of fcInf, fcNegInf:
      makeVal typ,  "0x" & toHex(cast[uint64](f))
    of fcNormal, fcSubnormal:
      var res = ""
      res.addFloatRoundtrip(f)
      if 'e' in res: # uses scientific notation?
        res = "0x" & toHex(cast[uint64](f)) # use hex notation
      makeVal typ, res
  of cnkPtrTy:
    unreachable("anonymous array location definition is not supported")
  of cnkArrayTy:
    let val {.cursor.} = m.get(v.val.StringId)
    var str = "c\""
    for it in val.items:
      str.addChar(it)
    # fill the remainder with NUL characters
    for _ in val.len..<m.unpackInt(m.tast[tn, 0].val):
      str.add "\\00"
    str.add "\""
    makeVal typeRefToC(m, typ, r), str
  of cnkOpaqueTy:
    # TODO: remove this case once foreign numeric types are gone
    let typ = typeRefToC(m, typ, r)
    let val =
      if v.kind == cnkInt: $m.unpackInt(v.val)
      else:                $m.unpackFloat(v.val)
    makeVal typ, val
  else:
    unreachable()

proc isAggregate(m; pos: NodeIndex): bool =
  let pos = resolve(m, pos)
  m.tast[pos].kind in {cnkArrayTy, cnkStructTy, cnkUnionTy}

proc callToC(m; pos; musttail: bool, r: var Writer): Value =
  ## Emits the C code for an argument list with `num` arguments.
  let len = m.ast.len(pos)
  var tpos = getType(m, pos)
  let typ = typeToC(m, tpos, r)

  discard advance(m.ast, pos) # skip the sub-tree head
  var fntype = getType(m, pos)
  if m.tast[fntype].kind == cnkPtrTy:
    fntype = m.resolve(m.tast.child(fntype, 0))

  let cconv = CallingConvToStr[CgCallConv(m.unpackUInt(m.tast[fntype, 0].val))]
  let callee = exprToReg(m, pos, r)
  var args = ""
  for i in 1..<len:
    if i > 1:
      args.add ", "

    let arg = exprToC(m, pos, r)
    if arg.typ.kind == tkAggregate:
      args.add "ptr byval("
      args.add arg.typ
      args.add ") "
      args.add arg.val
    else:
      args.add expectStorable(load(arg, r), r)

  if typ.kind == tkAggregate:
    # the value is returned through an out parameter
    let ret = r.newTemp()
    if args.len > 0:
      args.insert ", "

    if musttail:
      # forward the current out parameter
      r.add &"musttail call {cconv} void {callee.val}(ptr sret({typ}) %Result{args})\n"
      makeIndirect(typ, ret)
    else:
      r.add &"{ret} = alloca {typ}\n"
      r.add &"call {cconv} void {callee.val}(ptr sret({typ}) {ret}{args})\n"
      makeIndirect(typ, ret)
  elif typ.kind == tkVoid:
    if musttail:
      r.add "musttail "
    r.add &"call {cconv} void {callee.val}({args})\n"
    makeVal(VoidType, "")
  else:
    let ret = r.newTemp()
    if musttail:
      r.add &"{ret} = musttail call {cconv} {typ} {callee.val}({args})\n"
    else:
      r.add &"{ret} = call {cconv} {typ} {callee.val}({args})\n"
    makeVal(typ, ret)

proc checkedOpToC(m; pos; op: string, r: var Writer): Value =
  ## Emits the C code for a checked arithmetic operation.
  skip(m.ast, pos)
  let typ = typeRefToC(m, pos, r)
  let a = fitTo(exprToReg(m, pos, r), typ, r)
  let b = fitTo(exprToReg(m, pos, r), typ, r)
  let dst = exprToReg(m, pos, r)
  let tmp0 = r.newTemp()
  let tmp1 = r.newTemp()
  let tmp2 = r.newTemp()
  let agg = LLVMType(kind: tkAggregate, name: &"{{{typ}, i1}}")
  r.add &"{tmp0} = call {agg} {op}({a}, {b})\n"
  r.add &"{tmp1} = extractvalue {agg} {tmp0}, 0\n"
  r.add &"store {typ} {tmp1}, {dst}\n"
  r.add &"{tmp2} = extractvalue {agg} {tmp0}, 1\n"
  makeVal(BoolType, tmp2)

proc cmpToC(m; pos; sop, uop, fop: string, r: var Writer): Value =
  ## Emits the C code for a comparison.
  skip(m.ast, pos)
  let typ = primTypeRefToC(m, pos, r)
  let a = exprToReg(m, pos, r)
  let b = exprToReg(m, pos, r)
  let tmp = r.newTemp()
  case typ.kind
  of cnkIntTy:
    r.add &"{tmp} = icmp {sop} {typ} {a.val}, {b.val}\n"
  of cnkPtrTy, cnkUIntTy:
    r.add &"{tmp} = icmp {uop} {typ} {a.val}, {b.val}\n"
  of cnkFloatTy:
    r.add &"{tmp} = fcmp {fop} {typ} {a.val}, {b.val}\n"
  else:
    unreachable()
  makeVal BoolType, tmp

proc convToLLVM(m; pos; name: string, r: var Writer): Value =
  let typ = typeRefToC(m, pos, r)
  let arg = exprToReg(m, pos, r)
  let tmp = r.newTemp()
  r.add &"{tmp} = {name} {arg} to {typ}\n"
  makeVal typ, tmp

proc boolExprToLLVM(m; pos; r: var Writer): Value =
  ## Translates a CGIR bool expression to LLVM, returning an i1 register.
  result = load(exprToC(m, pos, r), r)
  if result.typ.width == 8:
    let tmp = r.newTemp()
    r.add &"{tmp} = trunc {result} to i1\n"
    result = makeVal(BoolType, tmp)

proc exprToC(m; pos; r: var Writer): Value =
  ## Emits the C code for expressions and symbols.
  let n = advance(m.ast, pos)
  case n.kind
  of cnkGlobal, cnkProc:
    makeVal PtrType, "@" & m.get(n.val.StringId)
  of cnkLocal:
    # parameters are handled separately
    makeVal PtrType, "%" & m.get(n.val.StringId)
  of cnkUse:
    # means load
    let typ = typeRefToC(m, pos, r)
    if m.ast[pos].kind == cnkLocal:
      let name = m.ast[pos].val.StringId
      let val = exprToC(m, pos, r)
      makeIndirect typ, val.val
    else:
      let val = exprToC(m, pos, r)
      if typ.kind == tkFunc:
        # the address is the value itself, no load is required
        makeVal typ, val.val
      else:
        makeIndirect typ, val.val
  of cnkDatum:
    makeVal PtrType, "@D" & $r.anon[n.val.Datum]
  of cnkValue:
    valueToC(m, pos, r)
  of cnkUnknown:
    skip(m.ast, pos)
    let name {.cursor.} = m.get(advance(m.ast, pos).val.StringId)
    case name
    of "errno":
      let tmp = r.newTemp()
      r.add &"{tmp} = load ptr, ptr @impl_errno\n"
      makeIndirect intType(32), tmp
    of "stdin", "stdout", "stderr":
      makeVal PtrType, "@impl_" & name
    of "_wenviron":
      makeVal PtrType, "@impl_wenviron"
    else:
      # just use the name verbatim
      makeVal PtrType, "@" & name
  of cnkNilLit:
    makeVal PtrType, "null"
  of cnkUnlikely:
    let arg = boolExprToLLVM(m, pos, r)
    let tmp = r.newTemp()
    r.add &"{tmp} = call i1 @llvm.expect({arg}, i1 false)\n"
    makeVal BoolType, tmp
  of cnkBitNot:
    skip(m.ast, pos)
    let val = exprToReg(m, pos, r)
    let tmp = r.newTemp()
    r.add &"{tmp} = xor {val}, -1\n"
    makeVal val.typ, tmp
  of cnkBitAnd: binOpToC(m, pos, "and", r)
  of cnkBitOr:  binOpToC(m, pos, "or", r)
  of cnkBitXor: binOpToC(m, pos, "xor", r)
  of cnkShr:    binOpToC(m, pos, "ashr", "lshr", "", r)
  of cnkShl:    binOpToC(m, pos, "shl", r)
  of cnkEq:     cmpToC(m, pos, "eq", "eq", "ueq", r)
  of cnkLe:     cmpToC(m, pos, "sle", "ule", "ule", r)
  of cnkLt:     cmpToC(m, pos, "slt", "ult", "ult", r)
  of cnkNot:
    skip(m.ast, pos)
    let arg = exprToReg(m, pos, r)
    let tmp = r.newTemp()
    r.add &"{tmp} = icmp eq {arg}, 0\n"
    makeVal(BoolType, tmp)
  of cnkNeg:
    let typ = typeRefToC(m, pos, r)
    let arg = exprToReg(m, pos, r)
    let tmp = r.newTemp()
    if typ.kind in {tkFloat, tkDouble}:
      r.add &"{tmp} = fneg {arg}\n"
    else:
      r.add &"{tmp} = sub nsw {typ} 0, {arg.val}\n"
    makeVal typ, tmp
  of cnkAdd:    binOpToC(m, pos, "add", "add", "fadd", r)
  of cnkSub:    binOpToC(m, pos, "sub", "sub", "fsub", r)
  of cnkMul:    binOpToC(m, pos, "mul", "mul", "fmul", r)
  of cnkDiv:    binOpToC(m, pos, "sdiv", "udiv", "fdiv", r)
  of cnkMod:    binOpToC(m, pos, "srem", "urem", "frem", r)
  of cnkCheckedAdd: checkedOpToC(m, pos, "@llvm.sadd.with.overflow", r)
  of cnkCheckedSub: checkedOpToC(m, pos, "@llvm.ssub.with.overflow", r)
  of cnkCheckedMul: checkedOpToC(m, pos, "@llvm.smul.with.overflow", r)
  of cnkZext: convToLLVM(m, pos, "zext", r)
  of cnkSext: convToLLVM(m, pos, "sext", r)
  of cnkFToI: convToLLVM(m, pos, "fptosi", r)
  of cnkFToU: convToLLVM(m, pos, "fptoui", r)
  of cnkIToF: convToLLVM(m, pos, "sitofp", r)
  of cnkUToF: convToLLVM(m, pos, "uitofp", r)
  of cnkTrunc: convToLLVM(m, pos, "trunc", r)
  of cnkPromote: convToLLVM(m, pos, "fpext", r)
  of cnkDemote: convToLLVM(m, pos, "fptrunc", r)
  of cnkPtrCast:
    let typ = typeRefToC(m, pos, r)
    let val = exprToReg(m, pos, r)
    if val.typ.kind == tkInt:
      let tmp = r.newTemp()
      r.add &"{tmp} = inttoptr {val} to {typ}\n"
      makeVal typ, tmp
    elif typ.kind == tkInt:
      let tmp = r.newTemp()
      r.add &"{tmp} = ptrtoint {val} to {typ}\n"
      makeVal typ, tmp
    else:
      # both types can only be pointers, and all pointers are the same; a no-op
      val
  of cnkBitcast:
    let typ = typeRefToC(m, pos, r)
    let val = exprToReg(m, pos, r)
    if val.typ.kind != typ.kind:
      let tmp = r.newTemp()
      r.add &"{tmp} = bitcast {val} to {typ}\n"
      makeVal typ, tmp
    else:
      # the types can only be the same; the cast is a no-op
      val
  of cnkConv:
    # a C-style conversion
    let dst = toPrimitive(m, m.types[advance(m.ast, pos).val.StringId])
    let src = toPrimitive(m, getType(m, pos))
    let typ = toLLVM(dst)
    let val = exprToReg(m, pos, r)
    case dst.kind
    of cnkIntTy, cnkUIntTy:
      case src.kind
      of cnkFloatTy:
        if dst.kind == cnkIntTy:
          let tmp = r.newTemp()
          r.add &"{tmp} = fptosi {typ}, {val}\n"
          makeVal typ, tmp
        else:
          let tmp = r.newTemp()
          r.add &"{tmp} = fptoui {typ}, {val}\n"
          makeVal typ, tmp
      of cnkIntTy, cnkUIntTy:
        if src.width < dst.width:
          if dst.kind == cnkUIntTy:
            let tmp = r.newTemp()
            r.add &"{tmp} = zext {val} to {typ}\n"
            makeVal typ, tmp
          else:
            let tmp = r.newTemp()
            r.add &"{tmp} = sext {val} to {typ}\n"
            makeVal typ, tmp
        elif src.width == dst.width:
          val # a no-op
        else:
          let tmp = r.newTemp()
          r.add &"{tmp} = trunc {val} to {typ}\n"
          makeVal typ, tmp
      of cnkPtrTy:
        let tmp = r.newTemp()
        r.add &"{tmp} = ptrtoint {typ}, {val}\n"
        makeVal typ, tmp
      of cnkOpaqueTy:
        unreachable("unsupported conversion source: " & m.get(src.name))
      else:
        unreachable("unsupported conversion source: " & $src)
    of cnkFloatTy:
      case src.kind
      of cnkFloatTy:
        if src.width == dst.width:
          val
        elif src.width > dst.width:
          let tmp = r.newTemp()
          r.add &"{tmp} = fptrunc {typ}, {val}\n"
          makeVal typ, tmp
        else:
          let tmp = r.newTemp()
          r.add &"{tmp} = fpext {typ}, {val}\n"
          makeVal typ, tmp
      of cnkIntTy:
        let tmp = r.newTemp()
        r.add &"{tmp} = sitofp {typ}, {val}\n"
        makeVal typ, tmp
      of cnkUIntTy:
        let tmp = r.newTemp()
        r.add &"{tmp} = uitofp {typ}, {val}\n"
        makeVal typ, tmp
      else:
        unreachable("unsupported conversion source: " & $src)
    of cnkPtrTy:
      case src.kind
      of cnkPtrTy:
        val # a no-op
      of cnkIntTy, cnkUIntTy:
        let tmp = r.newTemp()
        r.add &"{tmp} = inttoptr {typ}, {val}\n"
        makeVal typ, tmp
      of cnkOpaqueTy:
        unreachable("unsupported conversion source: " & m.get(src.name))
      else:
        unreachable("unsupported conversion source: " & $src)
    of cnkOpaqueTy:
      unreachable(m.get(dst.name))
    else:
      unreachable("unsupported conversion target: " & $dst)
  of cnkLoad:
    let typ = typeRefToC(m, pos, r)
    let arg = exprToReg(m, pos, r)
    # the actual loading is handled by the callsite
    makeIndirect typ, arg.val
  of cnkAddr:
    skip(m.ast, pos)
    let val = exprToC(m, pos, r)
    # the value becomes a pointer value
    makeVal PtrType, val.val
  of cnkCall:
    dec pos
    callToC(m, pos, false, r)
  of cnkSizeof:
    let typ = typeRefToC(m, pos, r)
    let other = m.types[advance(m.ast, pos).val.StringId]
    let (size, _) = computeSizeAlign(m, other)
    makeVal typ, $size
  of cnkAlignof:
    let typ = typeRefToC(m, pos, r)
    let other = m.types[advance(m.ast, pos).val.StringId]
    let (_, align) = computeSizeAlign(m, other)
    makeVal typ, $align
  of cnkOffsetof:
    let typ = typeRefToC(m, pos, r)
    let inner = advance(m.ast, pos).val.StringId
    for _ in 2..<len(n):
      skip(m.ast, pos)
    echo "offsetof is not implemented"
    makeVal typ, "0"
  of cnkPath:
    pathToC(m, pos, len(n) - 2, r)
  of AllNodes - cnkExprs -
     {cnkUnknown, cnkUnlikely, cnkDatum, cnkProc, cnkGlobal, cnkLocal}:
    unreachable(n.kind)

proc stmtToC(m; pos; r: var Writer): bool =
  ## Emits the C code for statements and blocks.
  result = true # statement returns, unless stated otherwise
  let n = advance(m.ast, pos)
  case n.kind
  of cnkStmtList:
    for _ in 0..<len(n):
      result = stmtToC(m, pos, r)
  of cnkDef:
    var align = readInt(m, m.ast, pos)
    let flags = readSet(m, m.ast, pos, CgLocAttrib)
    let typName = advance(m.ast, pos).val.StringId
    if align == 0:
      # take the alignment from the type
      let (_, a) = computeSizeAlign(m, m.types[typName])
      align = a

    let typ = typeRefToC(m, typName, r)
    let name = advance(m.ast, pos).val.StringId

    r.add &"%{m.get(name)} = alloca {typ}, align {align}\n"
    # r.add &"  #dbg_declare()\n"
  of cnkUnreachable:
    r.add "unreachable\n"
    result = false
  of cnkDrop:
    discard exprToC(m, pos, r)
  of cnkEmit:
    for _ in 0..<len(n):
      case m.ast[pos].kind
      of cnkString:
        # it's a code snippet that's to be used verbatim
        r.add m.get(advance(m.ast, pos).val.StringId)
      of cnkType:
        r.add typeRefToC(m, pos, r)
      else:
        r.add exprToC(m, pos, r)
  of cnkAsm:
    # XXX: LLVM does support inline assembler very similar to GNU inline asm,
    #      meaning that supporting asm is not impossible
    echo "unsupported asm statement"
    for _ in 0..<len(n):
      skip(m.ast, pos)
  of cnkScope:
    # has no effect
    # TODO: keep track of all scopes and live locals and emit
    #       `@llvm.lifetime.end` calls when leaving the scope (either directly
    #       or via a jump)
    result = stmtToC(m, pos, r)
  of cnkDispatch:
    let val = exprToReg(m, pos, r)
    let default = r.newLabel()
    r.add "switch "
    r.add val
    r.add ", label %"
    r.add default
    r.add "[ "
    var labels: seq[string]
    var hasDefault = false
    let save = pos
    # emit the gotos:
    for _ in 1..<len(n):
      let dest = advance(m.ast, pos)
      if len(dest) == 1:
        hasDefault = true
      else:
        let lab = r.newLabel()
        for _ in 1..<len(dest):
          let val = exprToC(m, pos, r)
          # the input is a NimSkull boolean
          if val.val == "true":
            r.add "i8 1"
          elif val.val == "false":
            r.add "i8 0"
          else:
            r.add val
          r.add ", label %"
          r.add lab
          r.add " "
        labels.add lab
      skip(m.ast, pos)

    r.add "]\n"
    pos = save
    # emit the bodies:
    for i in 1..<len(n):
      let dest = advance(m.ast, pos)
      # skip the values
      for _ in 1..<len(dest):
        skip(m.ast, pos)

      if len(dest) == 1:
        r.add default
        r.add ":\n"
      else:
        r.add labels[i - 1]
        r.add ":\n"
      discard stmtToC(m, pos, r)
      # the body always ends in a terminator

    if not hasDefault:
      r.add &"{default}:\n"
      r.add "unreachable\n"

    result = false
  of cnkAsgn:
    let dst = exprToC(m, pos, r)
    let epos = pos
    let src = exprToC(m, pos, r)
    if src.typ.kind == tkAggregate:
      let (size, _) = computeSizeAlign(m, getType(m, epos))
      r.add &"call void @llvm.memcpy(ptr {dst.val}, ptr {src.val}, i32 {size}, i1 false)\n"
    else:
      # everything mutable is a pointer
      r.add &"store {expectStorable(load(src, r), r)}, ptr {dst.val}\n"
  of cnkStore:
    let dst = exprToReg(m, pos, r)
    let epos = pos
    let src = exprToC(m, pos, r)
    if src.typ.kind == tkAggregate:
      let (size, _) = computeSizeAlign(m, getType(m, epos))
      r.add &"call void @llvm.memcpy({dst}, ptr {src.val}, i32 {size}, i1 false)\n"
    else:
      # everything mutable is a pointer
      r.add &"store {expectStorable(load(src, r), r)}, {dst}\n"
  of cnkBreak:
    r.add &"br label %{r.labels[advance(m.ast, pos).val]}\n"
    result = false
  of cnkBlock:
    let got = r.pushLabel(advance(m.ast, pos).val)
    if stmtToC(m, pos, r):
      r.add &"br label %{got}\n"
    r.add &"{got}:\n"
  of cnkIf:
    let cond = boolExprToLLVM(m, pos, r)
    let then = r.newLabel()
    let els = r.newLabel()
    r.add &"br {cond}, label %{then}, label %{els}\n"
    r.add &"{then}: ; then\n"
    result = stmtToC(m, pos, r)
    if len(n) == 3:
      if result:
        let exit = r.newLabel()
        r.add &"br label %{exit}\n"
        r.add &"{els}: ; else\n"
        if stmtToC(m, pos, r):
          r.add &"br label %{exit}\n"
        r.add &"{exit}: ; exit\n"
      else:
        r.add &"{els}: ; else\n"
        result = stmtToC(m, pos, r)
    else:
      if result:
        r.add &"br label %{els}\n"
      r.add &"{els}: ; exit \n"
      result = true
  of cnkWhile:
    # TODO: emit better code for ``while true``
    let start = r.newLabel()
    let exit = r.newLabel()
    let next = r.newLabel()
    let cond = boolExprToLLVM(m, pos, r)
    r.add &"br label %{start}\n"
    r.add &"{start}:\n"
    r.add &"br {cond}, label %{next}, label %{exit}\n"
    r.add &"{next}:\n"
    if stmtToC(m, pos, r):
      r.add &"br label %{start}\n" # loop
    r.add &"{exit}:\n"
  of cnkReturn:
    if len(n) > 0:
      let epos = pos
      let val = exprToC(m, pos, r)
      if val.typ.kind == tkAggregate:
        let (size, _) = computeSizeAlign(m, getType(m, epos))
        r.add &"call void @llvm.memcpy(ptr %Result, ptr {val.val}, i32 {size}, i1 false)\n"
        r.add &"ret void\n"
      else:
        r.add &"ret {expectStorable(load(val, r), r)}\n"
    else:
      r.add "ret void\n"
    result = false
  of cnkCall:
    dec pos
    discard callToC(m, pos, false, r)
  of cnkTailCall:
    dec pos
    let val = callToC(m, pos, true, r)
    if val.typ.kind == tkAggregate:
      r.add "ret void\n"
    else:
      r.add &"ret {val}\n"
    result = false
  of cnkRaise, cnkCheckedCall, cnkCheckedCallAsgn, cnkTry:
    unreachable("unsupported statement")
  of AllNodes - cnkStmts - cnkBlocks:
    unreachable(n.kind)

proc `==`(a, b: LLVMType): bool =
  if a.kind != b.kind:
    return false

  case a.kind
  of tkPtr, tkFunc, tkOpaque, tkFloat, tkDouble, tkVoid: true
  of tkInt: a.width == b.width
  of tkAggregate: a.name == b.name

type ConstrBuilder = object
  # unions and their construction makes translation of aggregate constructions
  # very complicated, as their LLVM construction expression sometimes needs to
  # be a packed one, which, in turn, means that the enclosing one has to be
  # too and so forth
  tn: NodeIndex ## the constructed type
  pos: int
  sstate: SizeAlignState
  padding: int64
  isPacked: bool

  prev: LLVMType
  values: seq[string] ## length of the current run of same types
  typ: string
  body: string

proc initConstBuilder(typ: NodeIndex): ConstrBuilder =
  ConstrBuilder(tn: typ, sstate: initSizeAlign())

proc fold(typ: sink LLVMType, values: sink seq[string]): Value =
  let count = values.len
  if count > 1:
    var body = fmt"["
    for i, it in values.pairs:
      if i > 0:
        body.add ", "
      body.add typ
      body.add " "
      body.add it
    body.add "]"
    makeVal LLVMType(kind: tkAggregate, name: fmt"[{count} x {typ}]"), body
  else:
    makeVal typ, values[0]

proc makeHeterogeneous(bu: var ConstrBuilder) =
  if bu.values.len > 0:
    let val = fold(move bu.prev, move bu.values)
    bu.typ.add val.typ
    bu.body.add val

proc commitPadding(bu: var ConstrBuilder) =
  if bu.padding > 0:
    bu.makeHeterogeneous()
    if bu.typ.len > 0:
      bu.typ.add ", "
      bu.body.add ", "
    bu.typ.add fmt"[{bu.padding} x i8]"
    bu.body.add fmt"[{bu.padding} x i8] zeroinitializer"
    bu.padding = 0
    bu.isPacked = true

proc addPadding(bu: var ConstrBuilder, numBytes: int64) =
  bu.padding += numBytes

proc append(bu: var ConstrBuilder, m; val: sink Value) =
  # TODO: combine all run-lengths of the same type, not just the one
  #       at the start
  let ctyp =
    if m.tast[bu.tn].kind == cnkArrayTy:
      m.tast.child(bu.tn, 1)
    else:
      m.tast.child(m.tast.child(bu.tn, bu.pos + 1), 0)

  let prev = bu.sstate.alignment
  # TODO: use addField, so that over- and under-alignment are handled properly
  let (size, align) = computeSizeAlign(m, ctyp)
  let pad = bu.sstate.add(size, align)
  if val.val.startsWith("<"):
    # the value is packed and has an alignment of 1
    bu.sstate.alignment = prev

  bu.addPadding(pad)
  bu.commitPadding()

  if bu.typ.len > 0: # heterogeneous?
    bu.typ.add ", "
    bu.typ.add val.typ
  elif bu.values.len == 0:
    bu.values = @[val.val]
    bu.prev = val.typ
  elif val.typ != bu.prev:
    bu.makeHeterogeneous()
    bu.typ.add ", "
    bu.typ.add val.typ
  else:
    bu.values.add @[val.val]

  if bu.values.len == 0:
    if bu.body.len > 0:
      bu.body.add ", "
    bu.body.add val
  inc bu.pos

proc appendEmpty(bu: var ConstrBuilder, m; count: int) =
  let ctyp =
    if m.tast[bu.tn].kind == cnkArrayTy:
      m.tast.child(bu.tn, 1)
    else:
      assert count == 1
      m.tast.child(m.tast.child(bu.tn, bu.pos + 1), 0)

  let prev = bu.sstate.alignment
  # TODO: use addField, so that over- and under-alignment are handled properly
  let (size, align) = computeSizeAlign(m, ctyp)
  let pad = bu.sstate.add(size * count, align)
  bu.sstate.alignment = prev # the padding is a bunch of i8
  bu.addPadding(pad + size * count)
  inc bu.pos, count

proc finish(bu: sink ConstrBuilder, m; r: var Writer): Value =
  if m.tast[bu.tn].kind == cnkArrayTy:
    let diff = int(m.unpackInt(m.tast[bu.tn, 0].val) - bu.pos)
    if diff > 0:
      appendEmpty(bu, m, diff)
  else:
    for i in (bu.pos + 1)..<m.tast.len(bu.tn):
      appendEmpty(bu, m, 1)

  let (size, align) = computeSizeAlign(m, bu.tn)
  if bu.sstate.alignment != align:
    # add the trailing padding when the aggregate type is packed
    bu.addPadding(int(size - bu.sstate.size))

  bu.commitPadding()

  if bu.typ.len > 0:
    if bu.isPacked:
      makeVal LLVMType(kind: tkAggregate, name: "<{" & bu.typ & "}>"), "<{" & bu.body & "}>"
    else:
      makeVal LLVMType(kind: tkAggregate, name: "{" & bu.typ & "}"), "{" & bu.body & "}"
  else:
    fold(bu.prev, bu.values)

proc constrToC(m; pos; r: var Writer): Value =
  ## Emits the C code for a construction expression.
  let n = advance(m.ast, pos)
  case n.kind
  of cnkValue:
    valueToC(m, pos, r)
  of cnkProc, cnkGlobal, cnkDatum, cnkSizeof, cnkAlignof, cnkOffsetof, cnkAddr:
    # `exprToC` already implements these
    dec pos
    exprToC(m, pos, r)
  of cnkPtrCast:
    let typ = typeRefToC(m, pos, r)
    # can only be some simple expression
    let val = exprToC(m, pos, r)
    if val.typ.kind == tkInt:
      makeVal typ, fmt"inttoptr ({val} to {typ})"
    elif typ.kind == tkInt:
      makeVal typ, fmt"ptrtoint ({val} to {typ})"
    else:
      val # the ptrcast is a no-op
  of cnkNilLit:
    makeVal PtrType, "null"
  of cnkConstr:
    let typ = m.types[advance(m.ast, pos).val.StringId]
    if len(n) == 1:
      # special case: empty constructor
      var tn = typ
      return makeVal(typeToC(m, tn, r), "zeroinitializer")

    # because of union types, it's not possible to use the declared type
    var bu = initConstBuilder(typ)
    for i in 1..<len(n):
      append(bu, m, constrToC(m, pos, r))

    finish(bu, m, r)
  of cnkRecConstr:
    let typ = m.types[advance(m.ast, pos).val.StringId]
    # very simple implementation: for each slot, check whether any path touches
    # it. If yes, step into the slot and repeat, otherwise zero initialize
    # the slot
    proc step(m; tn: NodeIndex, candidates: seq[NodeIndex]; depth: int, r: var Writer): Value =
      case m.tast[tn].kind
      of cnkStructTy:
        var bu = initConstBuilder(tn)
        # go over all slots:
        for i in 1..<len(m.tast[tn]):
          var filtered: seq[NodeIndex]
          for it in candidates.items:
            if m.unpackInt(m.ast[it, depth].val) == i - 1:
              filtered.add it

          if filtered.len == 1 and m.ast.len(filtered[0]) == depth + 2:
            # the whole slot is initialized
            var temp = m.ast.child(filtered[0], depth + 1)
            append(bu, m, constrToC(m, temp, r))
          elif filtered.len > 0:
            let sub = step(m, m.resolve(m.tast.child(m.tast.child(tn, i), 0)), filtered, depth + 1, r)
            append(bu, m, sub)
          else:
            appendEmpty(bu, m, 1)

        finish(bu, m, r)
      of cnkArrayTy:
        makeVal VoidType, "<missing-array>"
      of cnkUnionTy:
        # works much like a single-element struct
        let (expectSize, expectAlign) = computeSizeAlign(m, tn)
        let i = 1 + m.unpackInt(m.ast[candidates[0], depth].val)
        let tn = m.resolve(m.tast.child(m.tast.child(tn, i), 0)) # type of the union element
        let (gotSize, gotAlign) = computeSizeAlign(m, tn)

        var val: Value
        if candidates.len == 1 and m.ast.len(candidates[0]) == depth + 2:
          var temp = m.ast.child(candidates[0], depth + 1)
          val = constrToC(m, temp, r)
        else:
          val = step(m, tn, candidates, depth + 1, r)

        if expectSize == gotSize and expectAlign == gotAlign and val.val[0] != '<':
          val
        else:
          # needs extra padding or is packed
          var typ = "{"
          var body = "{"
          var pad = expectSize - gotSize
          typ.add fmt"{val.typ}"
          body.add fmt"{val}"
          if pad != 0:
            # add a value to ensure the correct padding
            typ.add fmt", [{pad} x i8]"
            body.add fmt", [{pad} x i8] zeroinitializer"
            pad -= expectAlign

          typ.add "}"
          body.add "}"
          if gotAlign != expectAlign:
            # the union has to be packed
            typ.add ">"
            typ.insert "<"
            body.add ">"
            body.insert "<"
          makeVal LLVMType(kind: tkAggregate, name: typ), body
      else:
        unreachable(m.tast[tn].kind)

    var cand: seq[NodeIndex]
    for j in 1..<len(n):
      cand.add pos
      skip(m.ast, pos)

    step(m, resolve(m, typ), cand, 0, r)
  else:
    unreachable(n.kind)

proc genProcDecl(m; typ, name: StringId; r: var Writer) =
  ## Emits the C type and function declarator for `typ` `name`, and
  ## parameter list `params`.
  var pos = m.types[typ]
  let L = len(advance(m.tast, pos)) - 2
  r.add CallingConvToStr[CgCallConv(readUInt(m, m.tast, pos))]
  r.add " "
  let ret = typeToC(m, pos, r)
  let hasOut = ret.kind == tkAggregate
  if hasOut:
    r.add "void"
  else:
    r.add ret

  r.add " @"
  r.add m.get(name)
  r.add "("

  if hasOut:
    # the out parameter comes first
    r.add fmt"ptr sret({ret})"

  for i in 0..<L:
    if i > 0 or hasOut:
      r.add ", "
    if isAggregate(m, pos):
      r.add fmt"ptr byval({typeToC(m, pos, r)})"
    elif m.tast[pos].kind == cnkVarargs:
      skip(m.tast, pos)
      r.add "..."
    else:
      r.add typeToC(m, pos, r)
  r.add ")"

proc genProcDecl(m; typ, name: StringId, params: NodeIndex; r: var Writer) =
  ## Emits the C type and function declarator for `typ` `name`, and
  ## parameter list `params`.
  var pos = m.types[typ]
  let L = len(advance(m.tast, pos)) - 2
  r.add CallingConvToStr[CgCallConv(readUInt(m, m.tast, pos))]
  r.add " "
  let ret = typeToC(m, pos, r)
  let hasOut = ret.kind == tkAggregate
  if hasOut:
    r.add "void"
  else:
    r.add ret

  r.add " @"
  r.add m.get(name)
  r.add "("

  if hasOut:
    # the out parameter comes first
    r.add fmt"ptr sret({ret}) %Result"

  var ppos = params
  assert m.ast[ppos].kind == cnkParams
  let numParams = len(advance(m.ast, ppos))
  for i in 0..<numParams:
    if i > 0 or hasOut:
      r.add ", "

    let typ = typeToC(m, pos, r)
    if typ.kind == tkAggregate:
      r.add fmt"ptr byval({typ}) "
    else:
      r.add typ
      r.add " "
    inc ppos # skip the Param node
    let attribs = readSet(m, m.ast, ppos, CgParamAttrib)
    let name = advance(m.ast, ppos).val.StringId
    if CgParamAttrib.NoAlias in attribs:
      r.add "noalias "

    r.add "%"
    if typ.kind == tkAggregate:
      r.add m.get(name)
    else:
      # the actual local is created separately
      r.addInt i

  if numParams < L:
    r.add "..."
  r.add ")"

proc globalToC(m; pos; declareOnly: bool, r: var Writer) =
  ## Emits the C type, qualifiers, specifiers, and the declarator - but not
  ## the initializer - for a global.
  let n = advance(m.ast, pos)
  let storage = cast[CgStorage](readUInt(m, m.ast, pos))
  var align = readInt(m, m.ast, pos)
  let attribs = readSet(m, m.ast, pos, CgLocAttrib)
  let tn = m.types[m.ast[pos].val.StringId]
  let typ = typeRefToC(m, pos, r)
  let name = advance(m.ast, pos).val.StringId

  r.add "@"
  r.add m.get(name)
  r.add " = "

  if declareOnly:
    r.add "external "
  elif n.kind == cnkGlobalExp:
    r.add "default "
  elif n.kind == cnkGlobalDef:
    r.add "hidden "
  else:
    r.add "external "

  case storage
  of Normal:
    r.add "global "
  of Const:
    r.add "constant "
  of Thread:
    r.add "thread_local global "

  if declareOnly:
    r.add typ
    r.add " "
  else:
    if len(n) == 6:
      r.add constrToC(m, pos, r)
    else:
      r.add typ
      r.add " zeroinitializer"

  if align == 0:
    let (_, a) = computeSizeAlign(m, tn)
    align = a

  # always specify the alignment, given that the initializer's generated type
  # might have the wrong alignment
  r.add " align "
  r.addInt align
  r.add "\n"

type
  ModuleDesc* = object
    ## Describes the shape of a LLVM module, i.e., what entities need to be
    ## declared and defined and in what order.
    headers: seq[StringId]
    dataFwd: seq[Datum]
    data: seq[Datum]
    tdecls: seq[StringId]
    tdefs: seq[StringId]
    gdecls: seq[StringId]
    gdefs: seq[StringId]
    fdecls: seq[tuple[inlined: bool, name: StringId]]
    fdefs: seq[tuple[inlined: bool, name: StringId]]
    emit: Emit

proc initModuleDesc*(m: CgModule, procs, globals: seq[StringId],
                     emit: sink Emit): ModuleDesc =
  ## Creates a module description containing all functions and globals given
  ## by `procs` and `globals`, plus their dependencies.
  var decls, defs, headers: PackedSet[StringId]
  var data: Table[Datum, uint8]
    ## '1' means declared, '2' means defined. A uint8 is used over a bool
    ## due to the former having space for a default value

  # discovery of dependencies makes up the bulk of the work. All identifiers
  # that are going to appear in the C code need to be (at least) *declared*

  proc require(m; name: StringId, res: var ModuleDesc) {.closure.}
  proc requireProc(m; name: StringId, res: var ModuleDesc) {.closure.}
  proc requireGlobal(m; name: StringId, res: var ModuleDesc) {.closure.}
  proc requireDatum(m; d: Datum, res: var ModuleDesc) {.closure.}

  proc inclHeader(m; str: StringId, res: var ModuleDesc) =
    # add the header (if any) to the header list
    if m.get(str).len > 0 and not headers.containsOrIncl(str):
      res.headers.add(str)

  proc scanType(m; pos; res: var ModuleDesc) =
    let n = advance(m.tast, pos)
    case n.kind
    of cnkPtrTy:
      skip(m.tast, pos) # LLVM pointers don't specify the pointee
    of cnkProcTy:
      for _ in 0..<len(n):
        scanType(m, pos, res)
    of cnkType:
      require(m, n.val.StringId, res)
    of cnkArrayTy:
      skip(m.tast, pos)
      scanType(m, pos, res)
    of cnkStructTy, cnkUnionTy:
      skip(m.tast, pos)
      for _ in 1..<len(n):
        discard advance(m.tast, pos)
        scanType(m, pos, res)
        skip(m.tast, pos)
        skip(m.tast, pos)
        skip(m.tast, pos)
        skip(m.tast, pos)
    of cnkFloatTy, cnkIntTy, cnkUIntTy:
      skip(m.tast, pos)
    of cnkOpaqueTy:
      skip(m.tast, pos)
      skip(m.tast, pos)
    of cnkVarargs, cnkInt, cnkString, cnkVoidTy, cnkCharTy, cnkBoolTy:
      discard
    else:
      unreachable()

  proc require(m; name: StringId, res: var ModuleDesc) =
    var pos = m.types[name]
    case m.tast[pos].kind
    of cnkStructTy, cnkUnionTy:
      if not defs.containsOrIncl(name):
        # also mark as declared, so that no additional declaration is emitted
        scanType(m, pos, res)
        res.tdefs.add name
    of cnkArrayTy:
      # array types are always inlined
      scanType(m, pos, res)
    of cnkProcTy:
      discard
    elif not decls.containsOrIncl(name):
      scanType(m, pos, res)

  proc scanParams(m; name: StringId, res: var ModuleDesc) =
    var pos = m.types[name]
    scanType(m, pos, res)

  proc requireGlobal(m; name: StringId, res: var ModuleDesc) =
    if not decls.containsOrIncl(name):
      # keep scanning a little simpler by always pulling in the full type
      # definition, even if not needed by how the global is used
      require(m, m.ast[m.globals[name], 3].val.StringId, res)
      res.gdecls.add name

  proc scanBody(m; pos; res: var ModuleDesc) =
    ## Scans a statement/expression for proc, type, etc. dependencies and
    ## registers them.
    const Relevant = {cnkAlignof, cnkSizeof, cnkOffsetof, cnkLoad,
                      cnkProc, cnkGlobal, cnkDatum, cnkDef, cnkConv,
                      cnkPtrCast, cnkPath, cnkUnknown, cnkEmit}
    case m.ast[pos].kind
    of cnkAlignof, cnkSizeof:
      pos = m.ast.child(pos, 1)
      require(m, advance(m.ast, pos).val.StringId, res)
    of cnkOffsetof:
      let L = len(m.ast[pos])
      pos = m.ast.child(pos, 1)
      require(m, advance(m.ast, pos).val.StringId, res)
      # ignore the rest
      for _ in 2..<L:
        skip(m.ast, pos)
    of cnkLoad:
      # a C deref requires a complete type
      pos = m.ast.child(pos, 0)
      require(m, advance(m.ast, pos).val.StringId, res)
      scanBody(m, pos, res)
    of cnkConv, cnkPtrCast:
      # the type operand needs to be available
      pos = m.ast.child(pos, 0)
      require(m, advance(m.ast, pos).val.StringId, res)
      scanBody(m, pos, res)
    of cnkProc:
      requireProc(m, advance(m.ast, pos).val.StringId, res)
    of cnkGlobal:
      requireGlobal(m, advance(m.ast, pos).val.StringId, res)
    of cnkDatum:
      requireDatum(m, advance(m.ast, pos).val.Datum, res)
    of cnkDef:
      pos = m.ast.child(pos, 2)
      require(m, advance(m.ast, pos).val.StringId, res)
      skip(m.ast, pos)
    of cnkUnknown:
      pos = m.ast.child(pos, 0)
      inclHeader(m, advance(m.ast, pos).val.StringId, res)
      skip(m.ast, pos)
    of cnkPath:
      let n = advance(m.ast, pos)
      skip(m.ast, pos) # skip the result type
      var tn = getType(m, pos)
      # the root may be a pointer, which is automatically dereferenced first,
      # requiring a full definition
      if m.tast[tn].kind == cnkPtrTy:
        tn = m.tast.child(tn, 0)
        scanType(m, tn, res)
      for _ in 1..<len(n):
        scanBody(m, pos, res)
    of cnkEmit:
      # types used in emit statements pull in the full definition
      let len = len(advance(m.ast, pos))
      for _ in 0..<len:
        if m.ast[pos].kind == cnkType:
          var pos2 = m.types[advance(m.ast, pos).val.StringId]
          scanType(m, pos2, res)
        else:
          scanBody(m, pos, res)
    of AllNodes - Relevant:
      # go over the subtree but only process the relevant parts. This is
      # faster and requires less recursion than manually handling all
      # node kinds
      var last = ord(pos)
      while ord(pos) <= last:
        if m.ast[pos].kind in Relevant:
          let prev = ord(pos)
          scanBody(m, pos, res)
          last += (ord(pos) - prev) - 1
        else:
          if not isLeaf(m.ast[pos]):
            last += len(m.ast[pos])
          inc pos

  proc requireDatum(m; d: Datum, res: var ModuleDesc) =
    case data.getOrDefault(d, 0)
    of 0:
      # not yet seen
      var pos = m.data[d]
      # the full type of the datum is required
      require(m, m.ast[pos, 0].val.StringId, res)
      data[d] = 1
      # scan the input first
      scanBody(m, pos, res)
      res.data.add d
      data[d] = 2
    of 1:
      # cyclic dependency; add a forward declaration
      res.dataFwd.add d
      data[d] = 2
    of 2:
      discard "already defined, nothing to do"
    else:
      unreachable()

  proc requireProc(m; name: StringId, res: var ModuleDesc) =
    if not decls.containsOrIncl(name):
      var pos = m.procs[name]
      case m.ast[pos].kind
      of cnkProcDef:
        scanParams(m, m.ast[pos, 1].val.StringId, res)
        if Inline in m.toSet(m.ast[pos, 0].val, CgProcAttrib):
          # pull in the definition for inline functions so that the C compiler
          # can do the inlining
          pos = m.ast.last(pos)
          scanBody(m, pos, res)
          res.fdefs.add (true, name)
        else:
          res.fdecls.add (false, name)
      of cnkProcImp, cnkProcExp:
        scanParams(m, m.ast[pos, 1].val.StringId, res)
        res.fdecls.add (false, name)
      else:
        unreachable()

  proc scanEmits(m; emits: seq[NodeIndex], res: var ModuleDesc) =
    for it in emits.items:
      var pos = it
      scanBody(m, pos, res)

  # block all defined entities from having a declaration requested
  for it in globals.items:
    case m.ast[m.globals[it]].kind
    of cnkGlobalDef, cnkGlobalExp:
      decls.incl(it)
    of cnkGlobalImp:
      discard "nothing to do"
    else:
      unreachable()

  for it in procs.items:
    case m.ast[m.procs[it]].kind
    of cnkProcDef, cnkProcExp:
      decls.incl(it)
    of cnkProcImp:
      discard "nothing to do"
    else:
      unreachable()

  # no need to scan the extra include section emits; they cannot refer
  # to anything
  scanEmits(m, emit.types, result)

  # scan the entities in the order the sections they'll be emitted in
  # are arranged

  for it in globals.items:
    var pos = m.globals[it]
    case m.ast[pos].kind
    of cnkGlobalDef, cnkGlobalExp:
      result.gdefs.add it
      require(m, m.ast[pos, 3].val.StringId, result)
      if m.ast[pos].len == 6:
        pos = m.ast.child(pos, 5)
        scanBody(m, pos, result)
    of cnkGlobalImp:
      requireGlobal(m, it, result)
    else:
      unreachable()

  scanEmits(m, emit.globals, result)
  scanEmits(m, emit.procs, result)

  for it in procs.items:
    var pos = m.procs[it]
    case m.ast[pos].kind
    of cnkProcDef, cnkProcExp:
      scanParams(m, m.ast[pos, 1].val.StringId, result)
      scanBody(m, pos, result)
      result.fdefs.add (false, it)
    of cnkProcImp:
      if not containsOrIncl(decls, it):
        result.fdecls.add (false, it)
        scanParams(m, m.ast[pos, 1].val.StringId, result)
    else:
      unreachable()

  result.emit = emit

proc moduleToLLVM*(m: CgModule, desc: ModuleDesc): string =
  ## Generates the code for a full C translation unit for `m` and `desc`.
  ## `preamble` is text that's placed at the start of the unit.
  ## `withLineDir` controls whether C line directives are enabled.
  var r = Writer()

  # add the definitions for some C procedures
  r.add """
define private ptr @memcpy(ptr %0, ptr %1, i64 %2) alwaysinline {
  call void @llvm.memcpy(ptr %0, ptr %1, i64 %2, i1 false)
  ret ptr %0
}
define private ptr @memmove(ptr %0, ptr %1, i64 %2) alwaysinline {
  call void @llvm.memmove(ptr %0, ptr %1, i64 %2, i1 false)
  ret ptr %0
}
define private ptr @memset(ptr %0, i32 %1, i64 %2) alwaysinline {
  %4 = trunc i32 %1 to i8
  call void @llvm.memset(ptr %0, i8 %4, i64 %2, i1 false)
  ret ptr %0
}
"""

  r.add """
define private i8 @NIM_LIKELY(i8 %0) alwaysinline {
  %2 = call i8 @llvm.expect(i8 %0, i8 1)
  ret i8 %2
}
define private i8 @NIM_UNLIKELY(i8 %0) alwaysinline {
  %2 = call i8 @llvm.expect(i8 %0, i8 0)
  ret i8 %2
}
"""

  r.add """
@_O_BINARY = private constant i32 32768
"""

  # libc declarations
  r.add """
@impl_errno = external thread_local global ptr
@EINTR = private constant i32 4

@_IOFBF = private constant i32 0
@_IONBF = private constant i32 4

; the actual implementations for the standard streams are provided in a
; separate unit
@impl_stdin = external global ptr
@impl_stdout = external global ptr
@impl_stderr = external global ptr

@impl_wenviron = external global ptr
"""

  for name in desc.tdecls.items:
    let pos = m.types[name]
    case m.tast[pos].kind
    of cnkStructTy, cnkUnionTy, cnkArrayTy:
      r.add &"%T.{m.get(name)} = type opaque\n"
    of cnkProcTy:
      discard "nothing to do"
    else:
      unreachable()

  # emit a type declaration for all aggregate types:
  for name in desc.tdefs.items:
    var pos = m.types[name]
    case m.tast[pos].kind
    of cnkStructTy, cnkUnionTy, cnkArrayTy:
      r.add &"%T.{m.get(name)} = type {typeToC(m, pos, r)}\n"
    of cnkProcTy:
      discard "nothing to do"
    else:
      unreachable()

  # populate the datum suffix table. The idea with the table is to have names
  # that are stable across compilations as long as the module's content
  # doesn't change
  for name in desc.data.items:
    r.anon[name] = uint32(r.anon.len)

  # emit definitions for inline constants:
  for name in desc.data.items:
    let it = m.data[name]
    r.add &"@D{r.anon[name]} = private unnamed_addr constant "
    var pos = it
    let (_, align) = computeSizeAlign(m, m.types[m.ast[pos, 0].val.StringId])
    r.add constrToC(m, pos, r)
    r.add fmt", align {align}"
    r.add "\n"

  # emit the declarations for external globals:
  for name in desc.gdecls.items:
    var pos = m.globals[name]
    globalToC(m, pos, true, r)

  # emit the definitions for all globals part of the module:
  for name in desc.gdefs.items:
    var pos = m.globals[name]
    globalToC(m, pos, false, r)

  for (inlined, name) in desc.fdecls.items:
    assert not inlined
    let pos = m.procs[name]
    r.add "declare "
    if inlined:
      r.add "private " # only visible within the current LLVM module
    elif m.ast[pos].kind == cnkProcDef:
      # the symbol doesn't need to be visible outside the dynlib (if any)
      r.add "external hidden "
    else:
      r.add "external default "

    genProcDecl(m, m.ast[pos, 1].val.StringId, name, r)
    r.add "\n"

  # emit definitions for functions:
  for (inlined, name) in desc.fdefs.items:
    var pos = m.procs[name]
    r.add "define "
    if inlined:
      r.add "private " # only visible within the current LLVM module
    elif m.ast[pos].kind == cnkProcDef:
      # the symbol doesn't need to be visible outside the dynlib (if any)
      r.add "external hidden "
    else:
      r.add "external default "

    pos = m.ast.child(pos, 0)
    let attribs = m.readSet(m.ast, pos, CgProcAttrib)

    let typ = advance(m.ast, pos).val.StringId
    skip(m.ast, pos) # skip the name
    let params = pos
    genProcDecl(m, typ, name, params, r)
    r.add " "

    if NoInline in attribs:
      r.add "noinline "
    elif Inline in attribs:
      r.add "inlinehint "

    r.add "{\n"
    block:
      # in the CGIR, all parameters are proper locations (i.e., they have
      # an address). Conservatively commit all non-by-address parameters to
      # stack locations
      pos = params
      let ptype = resolve(m, m.types[typ])
      let n = advance(m.ast, pos)
      for i in 0..<len(n):
        discard advance(m.ast, pos) # skip over the param header node
        skip(m.ast, pos) # skip the attributes
        let name = advance(m.ast, pos).val.StringId
        var tpos = m.tast.child(ptype, i + 2)
        let typ = typeToC(m, tpos, r)
        # TODO: by-reference parameters should be marked as such in the CGIR,
        #       so that their pointer is not unnecessarily commited to a stack
        #       location here
        if typ.kind != tkAggregate:
          r.add &"%{m.get(name)} = alloca {typ}\n"
          r.add &"store {typ} %{i}, ptr %{m.get(name)}\n"

      r.nextTemp = len(n) + 1 # +1 because of the implicit entry label

    discard stmtToC(m, pos, r)
    r.add "}\n"
    # reset the procedure-local state:
    r.labels.clear()
    r.nextLabel = 0
    r.nextTemp = 0

  result = r.output
