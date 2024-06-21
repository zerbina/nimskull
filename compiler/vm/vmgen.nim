#
#
#           The Nim Compiler
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements the code generator for the VM.

# FIXME: the below comment doesn't reflect reality anymore; it needs to be
#        updated

# Important things to remember:
# - The VM does not distinguish between definitions ('var x = y') and
#   assignments ('x = y'). For simple data types that fit into a register
#   this doesn't matter. However it matters for strings and other complex
#   types that use the 'node' field; the reason is that slots are
#   re-used in a register based VM. Example:
#
#.. code-block:: nim
#   let s = a & b  # no matter what, create fresh node
#   s = a & b  # no matter what, keep the node
#
# Also *stores* into non-temporary memory need to perform deep copies:
# a.b = x.y
# We used to generate opcAsgn for the *load* of 'x.y' but this is clearly
# wrong! We need to produce opcAsgn (the copy) for the *store*. This also
# solves the opcLdConst vs opcAsgnConst issue. Of course whether we need
# this copy depends on the involved types.

import
  std/[
    intsets,
    strutils,
    tables
  ],
  compiler/ast/[
    renderer,
    types,
    ast,
    lineinfos,
    trees
  ],
  compiler/backend/[
    cgir
  ],
  compiler/modules/[
    magicsys,
    modulegraphs
  ],
  compiler/mir/[
    mirenv,
    mirtrees,
    mirtypes
  ],
  compiler/front/[
    msgs,
    options
  ],
  compiler/utils/[
    containers,
    idioms
  ],
  compiler/vm/[
    identpatterns,
    vmaux,
    vmdef,
    vmobjects,
    vmtypegen,
    vmtypes,
    # vmbuiltins
  ],
  experimental/[
    results
  ]

import std/options as std_options

from compiler/backend/compat import getInt, isOfBranch, skipConv, lastSon,
  getMagic, pick, numArgs

when defined(nimCompilerStacktraceHints):
  import std/stackframes
  import compiler/utils/debugutils

type
  VmGenResult* = Result[CodeInfo, VmGenDiag] ## Result of a vmgen invocation

  VmGenError = object of CatchableError
    diag: VmGenDiag

  LocalIndex = int32
  TPosition = distinct int

  TSlotKind = enum    # We try to re-use slots in a smart way to
                      # minimize allocations; however the VM supports arbitrary
                      # temporary slot usage. This is required for the parameter
                      # passing implementation.
    slotInt,          # slot is unused
    slotFloat,
    slotRef,
    slotAddress
    slotUninit

  RegInfo = object
    inUse: bool
    kind: TSlotKind

  LocalLoc = object
    ## The current state for a local.
    slot: LocalIndex ## the register that holds either the handle or value
    isIndirect: bool ## whether the local uses a handle while its value
                     ## would fit it into a register

  BlockKind = enum
    bkBlock   ## labeled block
    bkExcept  ## ``except`` clause
    bkFinally ## ``finally`` clause

  BlockInfo = object
    oldRegisterCount: int
      ## upper bound of allocated registers at the beginning of the block
    label: BlockId
    case kind: BlockKind
    of bkBlock, bkFinally:
      start: TPosition
    of bkExcept:
      discard

  BProc = object
    blocks: seq[BlockInfo]
      ## information about each block-like construct. Forms a stack
    exits: seq[tuple[label: BlockId, pos: TPosition]]
      ## jump instructions that need patching once the target instruction is
      ## known
    sym: PSym
    body: Body
      ## the full body of the current procedure/statement/expression
    # bestEffort: TLineInfo
    #   ## the source-code position to point to for internal failures where
    #   ## no line information is directly available
    regInfo: seq[RegInfo]

    locals: OrdinalSeq[LocalId, LocalLoc]
      ## current state of all locals

    pastJoin: bool
      ## whether the next instruction comes immediately after a join. This
      ## informs whether to allow instruction merging
      # XXX: silly approach; just remember the position of the last join
    overflows: seq[TPosition]

    # exception handling state:
    baseOffset: TPosition
      ## the bytecode position that instruction-to-EH mappings need to be
      ## relative to
    ehStart: uint32
    ehExits: seq[tuple[label: BlockId, pos: uint32]]
      ## EH instructions that need patching once position and type of the
      ## target EH instruction is known
    lastPath: CgNode
      ## the path corresponding to the previously emitted EH instruction
      ## sequence, or nil. Prevents excessive EH code duplication

  CodeGenCtx* = object
    ## Bundles all input, output, and other contextual data needed for the
    ## code generator
    prc: BProc

    # code-generator owned state:
    env*: MirEnv
    typeInfoCache*: TypeTranslationState

    # immutable input parameters:
    graph*: ModuleGraph
    config*: ConfigRef
    # features*: TSandboxFlags
    # module*: PSym

    # input-output parameters:
    code*: seq[TInstr]
    debug*: seq[TLineInfo]
    ehTable*: seq[HandlerTableEntry]
    ehCode*: seq[EhInstr]
    constants*: seq[VmConstant]
    types*: VmTypeEnv

    map*: SeqMap[ProcedureId, FunctionIndex]
    builtinMaps*: Table[string, FunctionIndex]

  TCtx = CodeGenCtx ## legacy alias

  Temp = object
    slot: int32
    isReal: bool

template imm32(x: untyped): int32 =
  int32(x)
template imm8(x: untyped): int8 =
  int8(x)
template imm16(x: untyped): int16 =
  int16(x)

const
  IrrelevantTypes = abstractInst + {tyStatic, tyEnum} - {tyTypeDesc}
    ## the set of types that are not relevant to the VM. ``tyTypeDesc``, while
    ## not relevant right now, is likely going to be in the future.

  LvalueExprKinds = {cnkConst, cnkGlobal, cnkLocal, cnkArrayAccess,
                     cnkTupleAccess, cnkFieldAccess, cnkObjUpConv,
                     cnkObjDownConv, cnkDeref, cnkDerefView, cnkLvalueConv}

  MagicsToKeep* = {mIsolate, mNLen..mNError, mMinI, mMaxI, mParseExprToAst, mParseStmtToAst,
                   mAbsI, mDotDot, mNGetType, mNSizeOf, mNLineInfo, mSetLengthSeq, mEnumToStr, mRepr, mBoolToStr}
    ## the set of magics that are kept as normal procedure calls and thus need
    ## an entry in the function table.
    # XXX: mNGetType, mNGetSize, and mNLineInfo *are* real magics, but their
    #      symbols must reach here for disambiguation. This needs to be solved
    #      differently

proc initCodeGen*(g: ModuleGraph): CodeGenCtx =
  CodeGenCtx(graph: g, config: g.config, env: initMirEnv(g), typeInfoCache: initTypeGen())

proc getOrCreate*(c: var TCtx, typ: PType;
                  noClosure = false): VmTypeId {.inline.} =
  getOrCreate(c.typeInfoCache, c.types, c.config, typ, noClosure)

func raiseVmGenError(diag: sink VmGenDiag) {.noinline, noreturn.} =
  raise (ref VmGenError)(diag: diag)

func raiseVmGenError(
  diag: VmGenDiagKindAstRelated,
  n: PNode,
  instLoc = instLoc()
  ) =
  let d = VmGenDiag(kind: diag, location: n.info, ast: n, instLoc: instLoc)
  raise (ref VmGenError)(diag: d)

func raiseVmGenError(
  diag: sink VmGenDiag,
  loc:  TLineInfo,
  inst: InstantiationInfo
  ) {.noinline, noreturn.} =
  diag.location = loc
  diag.instLoc = inst
  raise (ref VmGenError)(diag: diag)

func fail(
  info: TLineInfo,
  kind: VmGenDiagKind,
  loc:  InstantiationInfo = instLoc()
  ) {.noinline, noreturn.} =
  raiseVmGenError(
    VmGenDiag(kind: kind),
    info,
    loc)

func fail(
  info: TLineInfo,
  kind: VmGenDiagKindAstRelated,
  ast:  PNode,
  loc:  InstantiationInfo = instLoc()
  ) {.noinline, noreturn.} =
  raiseVmGenError(
    VmGenDiag(kind: kind, ast: ast),
    info,
    loc)

func fail(
  info: TLineInfo,
  kind: VmGenDiagKindSymRelated,
  sym:  PSym,
  loc:  InstantiationInfo = instLoc()
  ) {.noinline, noreturn.} =
  raiseVmGenError(
    VmGenDiag(kind: kind, sym: sym),
    info,
    loc)

func fail(
  info:  TLineInfo,
  kind:  VmGenDiagKindMagicRelated,
  magic: TMagic,
  loc:   InstantiationInfo = instLoc()
  ) {.noinline, noreturn.} =
  raiseVmGenError(
    VmGenDiag(kind: kind, magic: magic),
    info,
    loc)

template tryOrReturn(code): untyped =
  try:
    code
  except VmGenError as e:
    return VmGenResult.err(move e.diag)

# forward declarations
proc genType(c: var TCtx, typ: PType; noClosure = false): int
func fitsRegister(t: PType): bool
proc load(c: var TCtx, info: TLineInfo, typ: PType)

template `[]`(p: BProc, id: LocalId): LocalLoc =
  ## Convenience shorthand.
  p.locals[id]

proc routineSignature(s: PSym): PType {.inline.} =
  ## Returns the signature type of the routine `s`
  if s.kind == skMacro: s.internal
  else:                 s.typ

func underlyingLoc(n: CgNode): CgNode =
  ## Computes and returns the symbol of the complete location (i.e., a location
  ## not part of a compound location) that l-value expression `n` names. If no
  ## complete location is named, ``nil`` is returned.
  var root {.cursor.} = n
  # skip nodes that don't change the location until we arrive at either one
  # that does, or a symbol
  while root.kind == cnkLvalueConv:
    root = root.operand

  result = root

func analyseIfAddressTaken(n: CgNode, prc: var BProc) =
  ## Recursively traverses the tree `n` and marks locals of which the address is
  ## taken as requiring indirection.
  case n.kind
  of cnkHiddenAddr, cnkAddr:
    # the nodes we're interested
    let loc = underlyingLoc(n.operand)
    # we're only interested in locals
    if loc.kind == cnkLocal:
      prc[loc.local].isIndirect = true
    else:
      # the operand expression must still be anaylsed
      analyseIfAddressTaken(n.operand, prc)
  of cnkAtoms:
    discard "ignore"
  of cnkWithOperand - {cnkHiddenAddr, cnkAddr}:
    analyseIfAddressTaken(n.operand, prc)
  of cnkWithItems:
    for it in n.items:
      analyseIfAddressTaken(it, prc)


func isNimNode(t: PType): bool =
  ## Returns whether `t` is the ``NimNode`` magic type
  let t = skipTypes(t, IrrelevantTypes)
  t.sym != nil and t.sym.magic == mPNimrodNode


func instr*(c: var TCtx; i: TLineInfo; opc: Opcode) =
  let ins = opc.TInstrType
  c.code.add(TInstr ins)
  c.debug.add(i)
  c.prc.pastJoin = false

func instr(c: var TCtx; i: TLineInfo; opc: TOpcode; a: int32) =
  let ins = (opc.TInstrType or (a.TInstrType shl regAShift))
  c.code.add(TInstr ins)
  c.debug.add(i)
  c.prc.pastJoin = false

func instr*(c: var TCtx; i: TLineInfo; opc: TOpcode; a: int32, b: int8) =
  let ins = (opc.TInstrType or (a.TInstrType shl regAShift) or (b.TInstrType shl regBShift))
  c.code.add(TInstr ins)
  c.debug.add(i)
  c.prc.pastJoin = false

func instr*(c: var TCtx; i: TLineInfo; opc: TOpcode; a: int8) =
  let ins = (opc.TInstrType or (a.TInstrType shl regBShift))
  c.code.add(TInstr ins)
  c.debug.add(i)
  c.prc.pastJoin = false

func instr*(c: var TCtx; i: TLineInfo; opc: TOpcode; a: int32, b: int16) =
  let ins = (opc.TInstrType or (a.TInstrType shl regAShift) or (b.TInstrType shl regBShift))
  c.code.add(TInstr ins)
  c.debug.add(i)
  c.prc.pastJoin = false

proc xjmp(c: var TCtx; n: CgNode; opc: TOpcode; a: int8 = 0): TPosition =
  result = TPosition(c.code.len)
  c.instr(n.info, opc, imm32 0, imm8 a)

func genLabel(c: TCtx): TPosition =
  result = TPosition(c.code.len)

proc jmpBack(c: var TCtx, n: CgNode, p = TPosition(0)) =
  let dist = p.int - c.code.len
  # internalAssert(c.config, regBxMin < dist and dist < regBxMax)
  c.instr(n.info, opcJmp, imm32 dist)

proc patchOpcode(instr: var TInstr, op: TOpcode) {.inline.} =
  instr = TInstr((instr.TInstrType and not regOMask) or TInstrType(op))

proc patchImm32(instr: var TInstr, imm: int32) =
  instr = ((instr.TInstrType and not (regAMask and not regOMask)).TInstrType or
               TInstrType(imm) shl regAShift).TInstr

proc patch(c: var TCtx, p: TPosition) =
  # patch with current index
  let p = p.int
  let diff = c.code.len - p
  # internalAssert(c.config, regBxMin < diff and diff < regBxMax)
  patchImm32(c.code[p], imm32 diff)
  c.prc.pastJoin = true

proc setupEh(c: var TCtx) =
  # the correct values are set at a later point
  c.prc.baseOffset = c.code.len.TPosition
  c.prc.ehStart = c.ehTable.len.uint32

proc genEhCode(c: var TCtx, n: CgNode)

proc registerEh(c: var TCtx, n: CgNode) =
  ## Emits an exception-handling table entry for the instruction at the head
  ## of the instruction list (i.e., the one emitted next). `n` must be either
  ## a label or target list.
  proc isEqual(a, b: CgNode): bool =
    ## Compares two label-like nodes for equality.
    if a.kind != b.kind:
      return false

    case a.kind
    of cnkLeave:  a[0].label == b[0].label
    of cnkLabel:  a.label == b.label
    of cnkResume: true
    else:
      unreachable()

  proc comparePaths(a, b: CgNode): int =
    ## Returns the number of actions `a` and `b` share at the end. 0
    ## means that both share no trailing actions.
    let (a, b) =
      if a.kind == cnkTargetList: (a, b)
      else:                       (b, a)
    # because of the above swap, if `a` is not a list of targets, then neither
    # is `b`
    if a.kind == cnkTargetList:
      if b.kind == cnkLabel:
        result = if isEqual(a[^1], b): 1 else: 0
      else:
        result = min(a.len, b.len)
        for i in 1..result:
          if not isEqual(a[^i], b[^i]):
            return i - 1
        # one target list is a subset of the other
    else:
      result = if isEqual(a, b): 1 else: 0

  let pos = uint32(c.code.len - c.prc.baseOffset.int)
  case n.kind
  of cnkLabel:
    # un-intercepted jump
    if c.prc.lastPath == nil or comparePaths(c.prc.lastPath, n) == 0:
      genEhCode(c, n)

    c.ehTable.add (pos, uint32(c.ehCode.len - 1))
  of cnkTargetList:
    if n.len == 1 and n[0].kind == cnkResume:
      # if there's nothing responding to the exception within the current
      # procedure, no EH code needs to be associated with the instruction
      return

    if c.prc.lastPath == nil or comparePaths(n, c.prc.lastPath) < n.len:
      # cannot re-use the previous instruction sequence
      genEhCode(c, n)

    c.ehTable.add (pos, uint32(c.ehCode.len - n.len))
  else:
    unreachable(n.kind)

proc getSlotKind(t: PType): TSlotKind =
  case t.skipTypes(IrrelevantTypes+{tyRange}).kind
  of tyBool, tyChar, tyInt..tyInt64, tyUInt..tyUInt64, tyPointer, tyNil,
     tyPtr:
    slotInt
  of tyRef:
    if isNimNode(t):
      slotRef
    else:
      slotInt
  of tyVar, tyLent:
    if t[0].skipTypes(IrrelevantTypes).kind == tyOpenArray:
      slotAddress # stored as an object
    else:
      slotInt # stored as a pointer
  of tyFloat..tyFloat64:
    slotFloat
  of tyProc:
    if t.callConv == ccClosure:
      slotAddress
    else:
      slotInt
  of tyTypeDesc:
    slotRef
  else:
    slotAddress

proc writeInstr(typ: PType): Opcode =
  case typ.skipTypes(IrrelevantTypes + {tyRange}).kind
  of tyInt, tyInt64, tyUInt, tyUInt64: opcWrInt64
  of tyInt32, tyUInt32: opcWrInt32
  of tyInt16, tyUInt16: opcWrInt16
  of tyInt8, tyUInt8, tyBool, tyChar: opcWrInt8
  of tyFloat, tyFloat64: opcWrFlt64
  of tyFloat32: opcWrFlt32
  of tyPointer, tyPtr, tyProc, tyVar, tyLent: opcWrInt64
  of tyRef:
    if typ.isNimNode(): opcWrRef
    else:               opcWrInt64
  else: unreachable(typ.skipTypes(IrrelevantTypes + {tyRange}).kind)

proc getFreeRegister(c: var BProc; k: TSlotKind): LocalIndex =
  for i in 0..<c.regInfo.len:
    if c.regInfo[i].kind == k and not c.regInfo[i].inUse:
      c.regInfo[i].inUse = true
      return LocalIndex(i)

  if c.regInfo.len >= high(LocalIndex):
    missing("error reporting")
    # fail(c.bestEffort, vmGenDiagTooManyRegistersRequired)

  c.regInfo.add RegInfo(inUse: true, kind: k)
  result = LocalIndex(c.regInfo.high)

func getTemp(cc: var TCtx; kind: TSlotKind): LocalIndex {.inline.} =
  getFreeRegister(cc.prc, kind)

proc getTemp(cc: var TCtx; tt: PType): LocalIndex =
  let typ = tt.skipTypes(abstractRange + {tyStatic})
  # we prefer the same slot kind here for efficiency. Unfortunately for
  # discardable return types we may not know the desired type. This can happen
  # for e.g. mNAdd[Multiple]:
  var kind = typ.getSlotKind
  if kind == slotAddress: kind = slotInt
  result = getFreeRegister(cc.prc, kind)

func freeTemp(c: var TCtx; r: LocalIndex) =
  c.prc.regInfo[r].inUse = false

func freeTemp(c: var TCtx; r: Temp) =
  if r.isReal:
    c.freeTemp(r.slot)

func isEmpty(prc: BProc, reg: LocalIndex): bool =
  prc.regInfo[reg].kind == slotUninit

proc gen(c: var TCtx; n: CgNode)

proc operand(c: var TCtx, n: CgNode) =
  gen(c, n)

proc genLvalue(c: var TCtx, n: CgNode)

func pushBlock(c: var TCtx, blk: sink BlockInfo) =
  blk.oldRegisterCount = c.prc.regInfo.len
  # XXX: ^^ the register list only grows, meaning that its length doesn't
  #      represent the allocated upper bound... Freeing register used for
  #      locals is broken in general
  c.prc.blocks.add blk

proc popBlock(c: var TCtx) =
  let blk = c.prc.blocks.pop()
  # free all register allocated for locals part of the block:
  for i in blk.oldRegisterCount..<c.prc.regInfo.len:
      # when not defined(release):
        # if c.prc.regInfo[i].inUse:
        #   doAssert false, "leaking temporary " & $i & " " & $c.prc.regInfo[i].kind
      c.prc.regInfo[i].inUse = false

func controlReg(c: TCtx, blk: BlockInfo): LocalIndex =
  c.code[blk.start.int].imm32

proc genGoto(c: var TCtx; n: CgNode) =
  ## Generates and emits the code for a ``cnkGoto``. Depending on whether it's
  ## an intercepted jump, the goto can translate to more than one instruction.
  let
    target = n[0]
    info = n.info
  case target.kind
  of cnkLabel:
    c.prc.exits.add (target.label, c.xjmp(n, opcJmp))
  of cnkTargetList:
    # there are some leave actions
    for i in 0..<target.len-1:
      let it = target[i]
      case it.kind
      of cnkLabel:
        # enter the finally section:
        c.prc.exits.add (it.label, c.xjmp(n, opcEnter))
      of cnkLeave:
        # leave the except or finally section:
        for blk in c.prc.blocks.items:
          if blk.label == it[0].label:
            case blk.kind
            of bkExcept:
              c.instr(info, opcLeave)
            of bkFinally:
              c.instr(info, opcLeave, imm32 c.controlReg(blk))
            else:
              unreachable()
            break
      else:
        unreachable()

    # the jump to the final destination
    c.prc.exits.add (target[^1].label, c.xjmp(n, opcJmp))
  else:
    unreachable()


iterator take[T](s: var seq[T], label: BlockId): lent T =
  ## Returns all items with `label` and removes them afterwards.
  var i = 0
  while i < s.len:
    if s[i].label == label:
      yield s[i]
      # remove the item from the list (order within the list doesn't
      # matter)
      s.del(i)
    else:
      inc i

proc patch(c: var TCtx, label: BlockId) =
  for it in take(c.prc.exits, label):
    c.patch(it.pos)

proc genIf(c: var TCtx, n: CgNode) =
  #  if (!expr1) goto lab1;
  #    thenPart
  #  lab1:
  c.operand(n[0])
  let start = c.xjmp(n[0], opcBranch) # if false
  # the 'if' opens a block, which the corresponding 'end' closes
  pushBlock(c): BlockInfo(kind: bkBlock, label: n[1].label, start: start)

# XXX `rawGenLiteral` should be a func, but can't due to `internalAssert`
proc rawGenLiteral(c: var TCtx, val: sink VmConstant): int =
  result = c.constants.len
  c.constants.add val
  # internalAssert c.config, result < regBxMax, "Too many constants used"

template cmpFloatRep(a, b: BiggestFloat): bool =
  ## Compares the bit-representation of floats `a` and `b`
  # Special handling for floats, so that floats that have the same
  # value but different bit representations are treated as different constants
  cast[uint64](a) == cast[uint64](b)
  # refs bug #16469
  # if we wanted to only distinguish 0.0 vs -0.0:
  # if a.floatVal == 0.0: result = cast[uint64](a.floatVal) == cast[uint64](b.floatVal)
  # else: result = a.floatVal == b.floatVal

template makeCnstFunc(name, vType, aKind, cmp) {.dirty.} =
  proc name(c: var TCtx, val: vType): int =
    for (i, cnst) in c.constants.pairs():
      if cnst.typ == aKind and cmp(cast[vType](cnst.val), val):
        return i

    c.rawGenLiteral: VmConstant(typ: aKind, val: cast[StackValue](val))

makeCnstFunc(toIntCnst, BiggestInt, akInt, `==`)
makeCnstFunc(toFloatCnst, BiggestFloat, akFloat, cmpFloatRep)

proc toIntCnst(c: var TCtx, val: Int128): int =
  # integer constants are stored as their raw bit representation
  toIntCnst(c, BiggestInt(toInt64(val)))

proc genLiteral(c: var TCtx, n: CgNode): int =
  case n.kind
  of cnkIntLit:   toIntCnst(c, n.intVal)
  of cnkUIntLit:  toIntCnst(c, n.intVal)
  of cnkFloatLit: toFloatCnst(c, n.floatVal)
  else:           unreachable(n.kind)

proc dup(c: var TCtx, info: TLineInfo) =
  # TODO: duplicate the instruction instead, if applicable
  c.instr(info, opcDup, imm8 1)

proc drop(c: var TCtx, info: TLineInfo) =
  # TODO: drop the previous instruction, if possible (when it has no side
  #       effects)
  c.instr(info, opcDrop)

proc capture(c: var TCtx, info: TLineInfo, kind: TSlotKind): Temp =
  if c.code.len > 0 and c.code[^1].opcode == opcGetLocal:
    result = Temp(slot: c.code[^1].imm32, isReal: false)
    c.code.setLen(c.code.len - 1)
    c.debug.setLen(c.debug.len - 1)
  elif c.code.len > 0 and c.code[^1].opcode == opcSetLocal:
    result = Temp(slot: c.code[^1].imm32, isReal: false)
    patchOpcode(c.code[^1], opcPopLocal)
  else:
    result = Temp(slot: c.getTemp(kind).int32, isReal: true)
    c.instr(info, opcPopLocal, result.slot)

proc getLocal(c: var TCtx, info: TLineInfo, name: int32) =
  if not(c.prc.pastJoin) and c.code.len > 0 and c.code[^1].opcode == opcPopLocal and c.code[^1].imm32 == name:
    c.code.setLen(c.code.len - 1)
    c.debug.setLen(c.debug.len - 1)
    c.instr(info, opcSetLocal, imm32 name)
  else:
    c.instr(info, opcGetLocal, imm32 name)

proc builtin(c: var TCtx, name: string, n: CgNode) =
  for i in 1..<n.len:
    c.operand(n[i])
  c.instr(n.info, opcCall, imm32 c.builtinMaps[name], imm16 n.len-1)
proc builtin(c: var TCtx, info: TLineInfo, name: string, num: int) =
  c.instr(info, opcCall, imm32 c.builtinMaps[name], imm16 num)

proc genCase(c: var TCtx; n: CgNode) =
  let selType = n[0].typ.skipTypes(abstractVarRange)
  c.operand(n[0])
  let tmp = c.capture(n.info, getSlotKind(n[0].typ))
  block:
    # iterate of/else branches
    for i in 1..<n.len:
      let branch = n[i]
      if isOfBranch(branch):
        let
          exit = branch[^1].label
        if selType.kind == tyString:
          # special handling for string case statements: generate a sequence
          # of comparisons

          for j in 0..<branch.len - 1:
            let it = branch[j]
            c.getLocal(it.info, tmp.slot)
            c.operand(it)
            # generate: ``if tmp == label: goto body``
            c.builtin(it.info, "__builtin_eqStr", 2)
            c.prc.exits.add (exit, c.xjmp(it, opcBranch, 1))

        else:
          # branch tmp, codeIdx
          # tjmp   thenLabel
          for j in 0..<branch.len - 1:
            let it = branch[j]
            if it.kind == cnkRange:
              c.operand(it[0])
              c.getLocal(it.info, tmp.slot)
              c.instr(it.info, opcLeInt)
              c.instr(it.info, opcGetLocal, tmp.slot)
              # XXX: use a branch instead?
              c.operand(it[1])
              c.instr(it.info, opcLeInt)
              c.instr(it.info, opcBitAnd)
            else:
              c.getLocal(it.info, tmp.slot)
              c.operand(it)
              c.instr(it.info, opcEqInt)
            c.prc.exits.add (exit, c.xjmp(it, opcBranch, 1))

      else:
        # else stmt:
        c.prc.exits.add (branch[0].label, c.xjmp(branch.lastSon, opcJmp))
  c.freeTemp(tmp)

proc genType(c: var TCtx; typ: PType; noClosure = false): int =
  ## Returns the ID of `typ`'s corresponding `VmType` as an `int`. The
  ## `VmType` is created first if it doesn't exist already
  result = c.getOrCreate(typ, noClosure).int

proc genEhCodeAux(c: var TCtx, n: CgNode) =
  ## Emits the EH instruction for a single action of a jump target list.
  case n.kind
  of cnkLeave:
    let label = n[0].label
    # which except or finally block?
    for it in c.prc.blocks.items:
      if it.label == label:
        case it.kind
        of bkExcept:
          c.ehCode.add (ehoLeave, 0'u16, 0'u32)
        of bkFinally:
          c.ehCode.add (ehoLeave, 1'u16, uint32 c.controlReg(it))
        else:
          unreachable()
        break
  of cnkLabel:
    # we don't know yet whether this is a finally or exception handler; the
    # instruction is patched later
    c.prc.ehExits.add (n.label, c.ehCode.len.uint32)
    c.ehCode.add (ehoNext, 0'u16, 0'u32)
  of cnkResume:
    # resume means to resume exception handling in the caller (if possible at
    # run-time)
    c.ehCode.add (ehoEnd, 0'u16, 0'u32)
  else:
    unreachable()

proc genEhCode(c: var TCtx, n: CgNode) =
  ## Emits the EH instruction sequence for a jump action description.
  case n.kind
  of cnkLabel:
    genEhCodeAux(c, n)
  of cnkTargetList:
    for i in 0..<n.len:
      genEhCodeAux(c, n[i])
  else:
    unreachable()
  # remember the jump target description the EH code sequence came from
  c.prc.lastPath = n

proc genExcept(c: var TCtx, n: CgNode) =
  ## Emits the EH code for a ``cnkExcept``.

  # simple but high-impact optimization: if the last EH exit we need to patch
  # is the preceding EH instruction, eliminate the instruction (it'd just be
  # a single instruction jump)
  if c.prc.ehExits.len > 0 and
     c.prc.ehExits[^1] == (n[0].label, c.ehCode.high.uint32):
    c.ehCode.setLen(c.ehCode.len - 1)
    c.prc.ehExits.setLen(c.prc.ehExits.len - 1)

  # patch all EH instructions targeting the handler:
  for it in take(c.prc.ehExits, n[0].label):
    c.ehCode[it.pos] = (ehoNext, 0'u16, c.ehCode.len.uint32 - it.pos)

  pushBlock(c): BlockInfo(kind: bkExcept, label: n[0].label)

  let pc = uint32 c.genLabel()
  if n.len > 1:
    # exception handler with filter
    for i in 1..<n.len-1:
      let it = n[i]
      assert it.kind == cnkType
      let typ = c.genType(it.typ.skipTypes(abstractPtrs))
      c.ehCode.add (ehoExceptWithFilter, uint16 typ, pc)

    # emit the follow-up EH code
    genEhCode(c, n[^1])
  else:
    # catch-all exception handler
    c.ehCode.add (ehoExcept, 0'u16, pc)
    # new EH code was emitted, invalidating the cached path:
    c.prc.lastPath = nil

proc genFinally(c: var TCtx, n: CgNode) =
  let pc = c.genLabel()

  # update all EH instructions targeting the finally:
  for it in take(c.prc.ehExits, n[0].label):
    c.ehCode[it.pos] = (ehoFinally, 0'u16, uint32 pc)

  pushBlock(c): BlockInfo(kind: bkFinally, label: n[0].label, start: pc)

  let control = c.getTemp(slotInt)
  c.patch(n[0].label) # patch the jumps targeting the finally
  c.instr(n.info, opcFinally, imm32 control)
  # the control register is freed at the end of the finally section

proc genRaise(c: var TCtx; n: CgNode) =
  if n[0].kind != cnkEmpty:
    c.operand(n[0])
    c.registerEh(n[^1])
    c.instr(n.info, opcRaise, imm8 0)
  else:
    # reraise
    c.registerEh(n[^1])
    c.instr(n.info, opcRaise, imm8 1)

func usesRegister(c: TCtx, s: LocalId): bool =
  ## Returns whether the location identified by `s` is backed by a register
  ## (that is, whether the value is stored in a register directly)
  fitsRegister(c.env[c.prc.body[s].typ]) and not c.prc[s].isIndirect

proc writeBackResult(c: var TCtx, info: TLineInfo) =
  ## If the result value is stored in a memory location (because it has its
  ## address taken, etc.), emits the code for storing it back into a
  ## register.
  let typ = c.env[c.prc.body[resultId].typ]
  if not isEmptyType(typ) and fitsRegister(typ):
    c.getLocal(info, imm32 c.prc[resultId].slot)
    if not usesRegister(c, resultId):
      c.load(info, typ)

proc genLit(c: var TCtx; n: CgNode) =
  let lit = genLiteral(c, n)
  c.instr(n.info, opcLdConst, imm32 lit)

proc genProcLit(c: var TCtx, n: CgNode) =
  c.instr(n.info, opcLdImmInt, imm32 c.map[n.prc].toFuncPtr)

import compiler/ast/typesrenderer

proc sizeof(c: TCtx, typ: PType): int =
  result = getSize(c.config, typ).int
  assert result >= 0, $typ

proc genCall(c: var TCtx; n: CgNode; withResultParam = false) =
  # an intermediate temporary might be needed
  var num = ord(withResultParam)
  let fntyp = n[0].typ.skipTypes(IrrelevantTypes)

  for i in 1..<(1 + numArgs(n)):
    # skip empty arguments (i.e. arguments to compile-time parameters that
    # were omitted):
    if n[i].kind != cnkEmpty:
      inc num
      c.operand(n[i])

  # the run-time callee operands come *after* the arguments
  if fntyp.callConv == ccClosure:
    # unpack the closure (i.e., tuple)
    c.operand(n[0])
    c.dup(n[0].info)
    c.instr(n[0].info, opcLdInt64, imm32 8) # env
    c.instr(n[0].info, opcSwap)
    c.instr(n[0].info, opcLdInt64, imm32 0) # proc pointer
  elif n[0].kind != cnkProc:
    c.operand(n[0])

  if n.kind == cnkCheckedCall:
    c.registerEh(n[^1])

  if n[0].kind == cnkProc:
    c.instr(n.info, opcCall, imm32 c.map[n[0].prc], imm16 num)
  elif fntyp.callConv == ccClosure:
    c.instr(n.info, opcIndCallCl, imm32 c.genType(n[0].typ, noClosure=true), imm16 num)
  else:
    c.instr(n.info, opcIndCall, imm32 c.genType(n[0].typ), imm16 num)

proc offsetof(c: TCtx, typ: PType, n: CgNode): int =
  discard getSize(c.config, typ) # make sure offsets were computed
  result = n.field.offset

proc offsetof(c: TCtx, typ: PType, i: int): int =
  let x = c.typeInfoCache.lookup(typ).unsafeGet
  result = c.types.fields[c.types[x].a.int + i].off.int

proc addImm(c: var TCtx, info: TLineInfo, val: Int128) =
  # TODO: coalesce with preceding AddImm instructions
  if val == 0:
    discard "would be a no-op; do nothing"
  elif val >= low(int32) and val <= high(int32):
    c.instr(info, opcAddImm, toInt32(val))
  else:
    c.instr(info, opcLdConst, imm32 c.toIntCnst(val))
    c.instr(info, opcAddInt)

proc genIndex(c: var TCtx; n: CgNode; arr: PType) =
  c.operand(n)
  if arr.skipTypes(abstractInst).kind == tyArray and (let x = firstOrd(c.config, arr);
      x != Zero):
    c.addImm(n.info, -x)

proc genNarrowUnsigned(c: var TCtx; info: TLineInfo, typ: PType)

proc rawLoad(c: var TCtx, info: TLineInfo, opc: TOpcode) =
  # if c.code.len > 0 and c.code[^1].opcode == opcAddImm:
  #   patchOpcode(c.code[^1], opc)
  # else:
  # TODO: the above optimization should help quite a bit, but it does the
  #       opposite! Investigate why
  c.instr(info, opc)

proc load(c: var TCtx, info: TLineInfo, typ: PType) =
  let size = getSize(c.config, typ)
  case typ.skipTypes(IrrelevantTypes).kind
  of tyFloat32..tyFloat64:
    if size == 8:
      c.rawLoad(info, opcLdFlt32)
    else:
      c.rawLoad(info, opcLdFlt64)
  else:
    case size
    of 8: c.rawLoad(info, opcLdInt64)
    of 4: c.rawLoad(info, opcLdInt32)
    of 2: c.rawLoad(info, opcLdInt16)
    of 1: c.rawLoad(info, opcLdInt8)
    else: unreachable()

    if not isUnsigned(typ) and size < 8:
      # sign-extend to the full register width
      c.instr(info, opcSignExtend, imm8 size*8)

proc genSym(c: var TCtx, n: CgNode, load = true)

proc genNarrow(c: var TCtx; n: CgNode) =
  ## If required for the type of `n`, emits a narrow/masking instruction for
  ## the value in `dest`. `sNarrow` is the opcode to use for signed integers.
  let
    t = skipTypes(n.typ, IrrelevantTypes + {tyRange})
    size = getSize(c.config, t)
  if size < 8:
    # the value doesn't occupy the full register's range
    if isUnsigned(t):
      c.instr(n.info, opcMask, imm8 (size*8))
    else:
      c.instr(n.info, opcSignExtend, imm8 size*8)

proc genNarrowU(c: var TCtx; n: CgNode) {.inline.} =
  # always mask the value, even if of signed type
  let size = getSize(c.config, skipTypes(n.typ, IrrelevantTypes + {tyRange}))
  if size < 8:
    c.instr(n.info, opcMask, imm8 (size*8))

proc genNarrowUnsigned(c: var TCtx; info: TLineInfo, typ: PType) =
  ## Only masks the value in `dest` (with ``opcNarrowU``) if `typ` is an
  ## unsigned integer type.
  let t = skipTypes(typ, IrrelevantTypes + {tyRange})
  if isUnsigned(t) and (let size = getSize(c.config, t); size < 8):
    c.instr(info, opcMask, imm8 size * 8)

proc binary(c: var TCtx, info: TLineInfo, op: Opcode, a, b: CgNode) =
  c.operand(a)
  c.operand(b)
  c.instr(info, op)

proc binary(c: var TCtx, op: Opcode, e: CgNode) =
  binary(c, e.info, op, e[1], e[2])

proc genAddSubInt(c: var TCtx, n: CgNode, opc: Opcode) =
  if n[2].kind in {cnkIntLit, cnkUIntLit}:
    c.operand(n[1])
    var v = getInt(n[2])
    if opc == opcSubInt:
      v = -v
    c.addImm(n.info, v)
  else:
    c.binary(opc, n)
  c.genNarrow(n)

proc genNumberConv(c: var TCtx, info: TLineInfo,
                   desttype, srctype: PType) =
  ## Generates and emits the code for an *unchecked* conversion between two
  ## numeric types.
  const
    Floats = {tyFloat..tyFloat64}
    Signed = {tyInt..tyInt64}
    Unsigned = {tyUInt..tyUInt64, tyChar, tyBool}

  # things to keep in mind:
  # - stack operands have no notion of signed vs. unsigned
  # - stack operands only store full-width integers and floats
  case desttype.kind
  of Signed:
    case srctype.kind
    of Floats:
      c.instr(info, opcFloatToSInt, imm8 desttype.size)
    of Signed, Unsigned:
      if desttype.size < srctype.size:
        c.instr(info, opcSignExtend, imm8 desttype.size * 8)
    else:
      unreachable()
  of Unsigned - {tyBool}:
    case srctype.kind
    of Floats:
      c.instr(info, opcFloatToUint, imm8 desttype.size)
    of Unsigned:
      if desttype.size < srctype.size:
        # truncate to the new size:
        c.instr(info, opcMask, imm8 (desttype.size * 8)-1)
    of Signed:
      # similar to the unsigned-to-unsigned case, but a narrow is also required
      # to "drop" the bits not part of the destination's bit range
      # XXX: this behaviour matches that of the C target, but truncating to the
      #      *source size* would make more sense
      if desttype.size < 8:
        # drop the bits past the destination's size
        c.instr(info, opcMask, imm8 (desttype.size * 8)-1)
    else:
      unreachable()
  of Floats:
    let op =
      case srctype.kind
      of Floats:   missing("float narrow")
      of Signed:   opcSIntToFloat
      of Unsigned: opcUIntToFloat
      else:        unreachable()

    c.instr(info, op, imm8 desttype.size)
  of tyBool:
    # compare the source operand against zero and invert
    case srctype.kind
    of Floats:
      c.instr(info, opcLdImmFloat, imm32 0)
      c.instr(info, opcEqFloat, imm8 1)
    of Signed, Unsigned:
      c.instr(info, opcLdImmInt, imm32 0)
      c.instr(info, opcEqInt, imm8 1)
    else:
      unreachable()
    c.instr(info, opcNot)
  else:
    unreachable()

proc genConv(c: var TCtx; n, arg: CgNode) =
  let
    a = skipTypes(n.typ, IrrelevantTypes + {tyRange})
    b = skipTypes(arg.typ, IrrelevantTypes + {tyRange})
  # we're not interested in range types here -- range checks are already
  # handled via ``opcRangeChck``

  c.operand(arg)
  # don't do anything for conversions that don't change the run-time type
  if not sameLocationType(a, b):
    case a.kind
    of IntegralTypes:
      genNumberConv(c, n.info, a, b)
    of tyPointer:
      discard "pointer conversion is a no-op"
    else:
      unreachable(a.kind)

proc genCast(c: var TCtx; n: CgNode) =
  const Signed = {tyInt..tyInt64, tyBool}
  const Unsigned = {tyUInt..tyUInt64, tyChar, tyPtr, tyRef, tyPointer}
  const Floats = {tyFloat..tyFloat64}
  let src = n.operand.typ.skipTypes(IrrelevantTypes)
  let dst = n.typ.skipTypes(IrrelevantTypes)
  c.operand(n.operand)

  if sameLocationType(src, dst):
    return # nothing to do

  let dstSize = getSize(c.config, dst)

  case dst.kind
  of Signed:
    case src.kind
    of Signed: discard "ignore"
    of Unsigned:
      if dstSize < sizeof(BiggestInt):
        c.instr(n.info, opcSignExtend, imm32 dstSize * 8)
    of Floats:
      if dstSize == 8:
        c.instr(n.info, opcReinterpI64)
      else:
        c.instr(n.info, opcReinterpI32)
        c.instr(n.info, opcSignExtend, imm8 32)
    else:
      # load from the memory address
      c.load(n.info, n.typ)
  of Unsigned:
    case src.kind
    of Signed, Unsigned:
      if dstSize < 8:
        # mask out the upper bits
        c.instr(n.info, opcMask, imm8 dstSize*8)
    of Floats:
      if dstSize == 8:
        c.instr(n.info, opcReinterpI64)
      else:
        c.instr(n.info, opcReinterpI32)
    else:
      # load from the memory address
      c.load(n.info, n.typ)
  of Floats:
    case src.kind
    of Signed, Unsigned:
      if dstSize < 8:
        # mask out the upper bits
        c.instr(n.info, opcMask, imm8 dstSize*8)
    of Floats:
      discard "illegal; ignore"
    else:
      # load from the memory address
      c.load(n.info, n.typ)
  else:
    # cast between complex types is a memcopy. To be safe, use the smaller size
    c.instr(n.info, opcLdImmInt, imm32 min(c.sizeof(n.typ), c.sizeof(n.operand.typ)))
    c.instr(n.info, opcMemCopy)


proc loadInt(c: var TCtx, info: TLineInfo, val: Int128) =
  ## Loads the integer `val` into `dest`, choosing the most efficient way to
  ## do so.
  if val in low(int32)..high(int32):
    # can be loaded as an immediate
    c.instr(info, opcLdImmInt, imm32 toInt(val))
  else:
    # requires a constant
    c.instr(info, opcLdConst, imm32 c.toIntCnst(val))

proc genSetElem(c: var TCtx, n: CgNode, first: Int128) =
  if first != 0:
    if n.kind in {cnkIntLit, cnkUIntLit}:
      c.loadInt(n.info, getInt(n) - first)
    else:
      c.operand(n)
      # XXX: inefficient bytecode, but this should be handled by the MIR
      #      anyway
      c.loadInt(n.info, first)
      c.instr(n.info, opcSubInt)

  else:
    c.operand(n)

proc genSetElem(c: var TCtx, n: CgNode, typ: PType) {.inline.} =
  ## `typ` is the type to derive the lower bound from
  let t = typ.skipTypes(abstractInst)
  assert t.kind == tySet

  # `first` can't be reliably derived from `n.typ` since the type may not
  # match the set element type. This happens with the set in a
  # `nkCheckedFieldExpr` for example
  let first = c.config.firstOrd(t)
  genSetElem(c, n, first)

func fitsRegister(t: PType): bool =
  getSlotKind(t) != slotAddress

proc unary(c: var TCtx, op: Opcode, n: CgNode) =
  c.operand(n[1])
  c.instr(n.info, op)

proc binaryArithOverflow(c: var TCtx, op: Opcode, n: CgNode) =
  c.operand(n[1])
  c.operand(n[2])
  c.instr(n.info, op)
  c.prc.overflows.add c.xjmp(n, opcBranch, 1)

proc binarySetOp(c: var TCtx, op: Opcode, n: CgNode) =
  c.operand(n[1])
  c.operand(n[2])
  c.instr(n.info, op, imm32 c.sizeof(n[1].typ))

proc binaryNarrowU(c: var TCtx, op: Opcode, n: CgNode) =
  c.binary(op, n)
  c.genNarrowUnsigned(n.info, n.typ)

proc genMagic(c: var TCtx; n: CgNode; m: TMagic) =
  case m
  of mSubI:
    c.genAddSubInt(n, opcSubInt)
  of mAddI:
    c.genAddSubInt(n, opcAddInt)
  of mOrd, mChr:
    c.operand(n[1])
  of mArrToSeq:
    c.builtin("arrToSeq", n)
  of mLengthOpenArray, mLengthArray, mLengthSeq:
    c.operand(n[1])
    # the length is stored in the first field; load it
    c.rawLoad(n.info, opcLdInt64)
  of mLengthStr:
    let t = n[1].typ.skipTypes(abstractInst)
    case t.kind
    of tyString:
      c.operand(n[1])
      # the length is stored in the first field; load it
      c.rawLoad(n.info, opcLdInt64)
    of tyCstring:
      c.builtin("lenCString", n)
    else:
      unreachable(t.kind)
  of mIncl:
    c.operand(n[1])
    c.operand(n[2])
    c.instr(n.info, opcIncl, imm32 c.sizeof(n[1].typ))
  of mExcl:
    c.operand(n[1])
    c.operand(n[2])
    c.instr(n.info, opcExcl, imm32 c.sizeof(n[1].typ))
  of mCard:
    c.operand(n[1])
    c.loadInt(n.info, getSize(c.config, n[1].typ).toInt128)
    c.builtin(n.info, "__card", 2)
  of mMulI: c.binaryArithOverflow(opcMulChck, n)
  of mDivI: c.binaryArithOverflow(opcDivChck, n)
  of mModI: c.binaryArithOverflow(opcModChck, n)
  of mAddF64: c.binary(opcAddFloat, n)
  of mSubF64: c.binary(opcSubFloat, n)
  of mMulF64: c.binary(opcMulFloat, n)
  of mDivF64: c.binary(opcDivFloat, n)
  of mShrI:
    # modified: genBinaryABC(c, n, dest, opcShrInt)
    # narrowU is applied to the left operandthe idea here is to narrow the left operand
    c.operand(n[1])
    c.genNarrowU(n)
    c.operand(n[2])
    c.instr(n.info, opcShr)
  of mShlI:
    c.binary(opcShl, n)
    genNarrow(c, n)
  of mAshrI: c.binary(opcAshr, n)
  of mBitandI: c.binary(opcBitAnd, n)
  of mBitorI: c.binary(opcBitOr, n)
  of mBitxorI: c.binary(opcBitXor, n)
  of mAddU: c.binaryNarrowU(opcAddInt, n)
  of mSubU: c.binaryNarrowU(opcSubInt, n)
  of mMulU: c.binaryNarrowU(opcMulInt, n)
  of mDivU: c.binaryNarrowU(opcDivU, n)
  of mModU: c.binaryNarrowU(opcModU, n)
  of mEqI, mEqB, mEqEnum, mEqCh:
    c.binary(opcEqInt, n)
  of mLeI, mLeEnum, mLeCh, mLeB:
    c.binary(opcLeInt, n)
  of mLtI, mLtEnum, mLtCh, mLtB:
    c.binary(opcLtInt, n)
  of mEqF64: c.binary(opcEqFloat, n)
  of mLeF64: c.binary(opcLeFloat, n)
  of mLtF64: c.binary(opcLtFloat, n)
  of mLePtr, mLeU: c.binary(opcLeu, n)
  of mLtPtr, mLtU: c.binary(opcLtu, n)
  of mEqRef:
    c.binary(opcEqInt, n)
  of mEqProc:
    # XXX: lower this as a MIR pass
    if skipTypes(n[1].typ, abstractInst).callConv == ccClosure:
      c.builtin("cmpClosure", n)
    else:
      c.binary(opcEqInt, n)
  of mXor:
    # TODO: really?
    c.binary(opcBitXor, n)
  of mNot:
    c.unary(opcNot, n)
  of mUnaryMinusI, mUnaryMinusI64:
    # emit the overflow check
    c.operand(n[1])
    c.dup(n[1].info)
    c.loadInt(n[1].info, c.config.firstOrd(n[1].typ))
    c.instr(n[1].info, opcEqInt)
    c.prc.overflows.add c.xjmp(n[1], opcBranch, imm8 1)
    c.instr(n.info, opcNegInt)
  of mBitnotI:
    c.unary(opcBitNot, n)
    c.genNarrowUnsigned(n.info, n.typ)
  of mCharToStr:
    c.operand(n[1])
    c.builtin(n.info, "__charToStr", 2)
  of mCStrToStr, mStrToCStr, mStrToStr:
    let val = n[1]
    if val.kind in LvalueExprKinds:
      # loading the handle into dest is wrong, the value needs to be
      # copied
      c.genLvalue(val)
    else:
      c.operand(val)
    c.instr(n.info, opcCopy, imm32 c.genType(n.typ))
  of mEqStr, mEqCString: c.builtin("__builtin_eqStr", n)
  of mLeStr: c.builtin("leStr", n)
  of mLtStr: c.builtin("ltStr", n)
  of mEqSet: c.binarySetOp(opcEqSet, n)
  of mLeSet: c.binarySetOp(opcLeSet, n)
  of mLtSet: c.binarySetOp(opcLtSet, n)
  of mMulSet: c.binarySetOp(opcMulSet, n)
  of mPlusSet: c.binarySetOp(opcPlusSet, n)
  of mMinusSet: c.binarySetOp(opcMinusSet, n)
  of mConStrStr:
    c.instr(n.info, opcStackAlloc, imm32 c.genType(n.typ))
    let tmp = c.getTemp(slotAddress)
    c.instr(n.info, opcPopLocal, imm32 tmp)
    for i in 1..<n.len:
      c.getLocal(n.info, imm32 tmp)
      c.operand(n[i])
      if n[i].typ.kind == tyChar:
        c.builtin(n.info, "__builtin_appendStrChar", 2)
      else:
        c.builtin(n.info, "__builtin_appendStrStr", 2)
    c.getLocal(n.info, imm32 tmp)
    c.instr(n.info, opcCopy, imm32 c.genType(n.typ))
    c.freeTemp(tmp)
  of mInSet:
    c.operand(n[1])
    c.genSetElem(n[2], n[1].typ)
    c.instr(n.info, opcInSet, imm32 c.sizeof(n[1].typ))
  of mIsNil:
    # XXX: lower this earlier
    c.operand(n[1])
    if skipTypes(n[1].typ, abstractInst).callConv == ccClosure:
      # load the procedure address first
      c.rawLoad(n.info, opcLdInt64)
    c.instr(n.info, opcLdImmInt, imm32 0)
    c.instr(n.info, opcEqInt)
  of mParseBiggestFloat:
    missing("parseBiggestFloat")
  of mDefault:
    case getSlotKind(n.typ)
    of slotInt:
      c.instr(n.info, opcLdImmInt, imm32 0)
    of slotFloat:
      c.instr(n.info, opcLdImmFloat, imm32 0)
    elif true:#needsDestroy(n.typ):
      # the destination operand was already loaded
      c.instr(n.info, opcReset, imm32 c.genType(n.typ))
    else:
      c.loadInt(n.info, toInt128 getSize(c.config, n.typ))
      c.instr(n.info, opcMemClear)

  of mOf:
    let t1 = n[1].typ.skipTypes(abstractRange)
    if t1.kind != tyRef:
      # XXX: the spec for `of` with non-ref types is missing, so we simply
      #      treat it as an `is` for now. If it's decided that this is the
      #      correct behaviour, the `of` should be eliminated in `sem` instead
      #      of down here
      c.instr(n.info, opcLdImmInt, imm32 ord(sameType(t1, n[2].typ)))
    else:
      let typ = n[2].typ.skipTypes(abstractPtrs)
      c.operand(n[1])
      c.instr(n.info, opcLdImmInt, imm32 c.genType(typ))
      c.builtin(n.info, "of", 2)
  of mHigh:
    case n[1].typ.skipTypes(abstractVar-{tyTypeDesc}).kind:
    of tyCstring:
      c.builtin("lenCString", n)
    else:
      c.operand(n[1])
      c.rawLoad(n.info, opcLdInt64)
    c.instr(n.info, opcAddImm, imm32(-1))
  of mEcho:
    for i in 2..<n.len-1:
      c.operand(n[i])
    c.instr(n.info, opcYield, imm32 (numArgs(n)-1), imm8 0)
  of mExpandToAst:
    let call = n
    let numArgs = numArgs(call)
    for i in 0..<numArgs:
      c.operand(n[1 + i])
    # XXX: getAst cannot have a valid signature (since it accepts an arbitrary
    #      amount of arguments), so the validation pass is guaranteed to
    #      fail...
    #      `transf` should create an array construction instead. While very
    #      inefficient, in terms of VM resources, it's the cleanest solution,
    #      not requiring the introduction of variable-argument procedures or
    #      syscall shenanigans
    c.instr(n.info, opcCall, imm32 c.map[n[0].prc], imm16 numArgs)
  of mSizeOf, mAlignOf, mOffsetOf:
    fail(n.info, vmGenDiagMissingImportcCompleteStruct, m)

  of mRunnableExamples:
    discard "just ignore any call to runnableExamples"
  of mDestroy, mTrace: discard "ignore calls to the default destructor"
  of mFinished:
    # XXX: the implementation is a hack -- it makes a lot of implicit
    #      assumptions and is thus very brittle. However, don't attempt to
    #      fix it here; implement the lowering of the ``mFinished`` magic as a
    #      MIR pass that is used for all backends
    c.operand(n[1])
    c.instr(n.info, opcLdInt64, imm32 8)
    c.instr(n.info, opcLdInt64, imm32 0)
    c.instr(n.info, opcLdImmInt, imm32 0)
    c.instr(n.info, opcEqInt)
  of mChckRange:
    c.operand(n[1])
    let tmp = c.capture(n.info, slotInt)
    c.getLocal(n.info, tmp.slot)
    c.operand(n[2])
    c.instr(n.info, opcLtInt)
    block:
      let jmp = c.xjmp(n, opcBranch)
      c.instr(n.info, opcRaise)
      c.patch(jmp)
    c.operand(n[3])
    c.instr(n.info, opcGetLocal, tmp.slot)
    c.instr(n.info, opcLtInt)
    block:
      let jmp = c.xjmp(n, opcBranch)
      c.instr(n.info, opcRaise)
      c.patch(jmp)
    c.instr(n.info, opcGetLocal, tmp.slot)
    c.freeTemp(tmp)
  of mChckNaN:
    discard "implementation is missing"
  of mChckIndex:
    case n[1].typ.skipTypes(IrrelevantTypes + {tyVar}).kind
    of tyString, tyCstring, tySequence:
      c.operand(n[1])
      c.rawLoad(n.info, opcLdInt64)
    of tyOpenArray, tyVarargs:
      c.operand(n[1])
      c.rawLoad(n.info, opcLdInt64)
    of tyArray:
      c.loadInt(n[1].info, lengthOrd(c.config, n[1].typ))
    else:
      unreachable(n[1].typ.skipTypes(IrrelevantTypes).kind)

    c.genIndex(n[2], n[1].typ)
    c.instr(n.info, opcLeu)
    let jmp = c.xjmp(n, opcBranch)
    c.instr(n.info, opcRaise) # TODO: incorrect
    c.patch(jmp)
  of mChckObj:
    echo "missing object check"
  of mChckField:
    c.operand(n[1])
    c.genSetElem(n[2], n[1].typ)
    c.instr(n.info, opcInSet, imm32 c.sizeof(n[1].typ))
    let jmp = c.xjmp(n, opcBranch, imm8 (1-n[3].intVal))
    # TODO: implement this properly
    c.instr(n.info, opcRaise)
    c.patch(jmp)
  of mChckBounds:
    echo "missing: bound check"
  of MagicsToKeep - mExpandToAst:
    c.genCall(n)
  of mAppendStrStr:
    c.operand(n[1])
    c.operand(n[2])
    c.builtin(n.info, "__builtin_appendStrStr", 2)
  of mAppendStrCh:
    c.operand(n[1])
    c.operand(n[2])
    c.builtin(n.info, "__builtin_appendStrChar", 2)
  of mAppendSeqElem:
    c.operand(n[1])
    c.loadInt(n.info, toInt128 c.genType(n[2].typ))
    c.builtin(n.info, "__prepareSeqAdd", 2)
    # copy the value
    # XXX: could move
    c.operand(n[2])
    if fitsRegister(n[2].typ):
      c.instr(n.info, writeInstr(n[2].typ))
    elif vtfDataOnly in c.types[VmTypeId c.genType(n[2].typ)].flags:
      c.loadInt(n.info, toInt128 c.sizeof(n[2].typ))
      c.instr(n.info, opcMemCopy)
    else:
      # manual move implementation
      let tmp = c.capture(n.info, slotAddress)
      c.getLocal(n.info, tmp.slot)
      c.loadInt(n.info, toInt128 c.sizeof(n[2].typ))
      c.instr(n.info, opcMemCopy)
      # clear the source
      c.getLocal(n.info, tmp.slot)
      c.loadInt(n.info, toInt128 c.sizeof(n[2].typ))
      c.instr(n.info, opcMemClear)
      c.freeTemp(tmp)


  of mNewSeq:
    c.operand(n[1])
    c.operand(n[2])
    c.instr(n.info, opcLdImmInt, imm32 c.genType(n[1].typ))
    c.builtin(n.info, "__newseq", 3)
  of mNewString:
    # the destination is on the operand stack already
    c.operand(n[1])
    c.builtin(n.info, "__newstr", 2)
  of mNew:
    c.instr(n.info, opcLdImmInt, imm32 c.types[VmTypeId c.genType(n.typ)].b)
    c.builtin(n.info, "__newobj", 1)
  of mNewStringOfCap, mNewSeqOfCap:
    c.operand(n[1])
    c.drop(n[1].info)
    c.instr(n.info, opcReset, imm32 c.genType(n.typ))
    # TODO: implement properly
  of mSetLengthStr:
    c.builtin("__builtin_strSetLen", n)
  of mUnaryPlusF64:
    # XXX: huh, why does it reach here?
    c.operand(n[1])
  else:
    echo "missing magic: ", m
    # mGCref, mGCunref, mFinished, etc.
    fail(n.info, vmGenDiagCodeGenUnhandledMagic, m)

func setSlot(c: var TCtx; v: LocalId): LocalIndex {.discardable.} =
  result = c.getTemp(c.env.types[c.prc.body[v].typ])
  c.prc[v].slot = result

func cannotEval(c: TCtx; n: CgNode) {.noinline, noreturn.} =
  # best-effort translation to ``PNode`` for improved error messages
  # XXX: move this kind of error reporting outside of vmgen instead
  {.cast(noSideEffect).}:
    let ast =
      if n.kind == cnkField:
        newSymNode(n.field, n.info)
      else:
        nil # give up

  raiseVmGenError(vmGenDiagCannotEvaluateAtComptime, ast)

proc importcCondVar*(s: PSym): bool {.inline.} =
  # see also importcCond
  if sfImportc in s.flags:
    return s.kind in {skVar, skLet, skConst}

proc putIntoLoc(c: var TCtx, e: CgNode, move: bool) =
  ## Generates and emits the code for assigning expression `e` to a memory
  ## location. `dest` and `idx` represent the destination location, with `wr`
  ## being the opcode for writing something to the location and `ld` the opcode
  ## for loading a handle to the location.
  ##
  ## Converting single-location views (``var`` and ``lent``) to pointer values
  ## is taken care of here, as well as handling `openArray` conversions.

  if fitsRegister(e.typ):
    c.operand(e)
    c.instr(e.info, writeInstr(e.typ))
  elif e.kind in LvalueExprKinds:
    # the source value is stored in an in-memory location
    c.genLvalue(e)
    if move:
      c.loadInt(e.info, toInt128 c.sizeof(e.typ))
      c.instr(e.info, opcMemCopy)
    else:
      c.instr(e.info, opcCopy, imm32 c.genType(e.typ))
  elif e.kind in {cnkCall, cnkCheckedCall} and e[0].kind != cnkMagic:
    # TODO: spawn a temporary for checked calls
    c.genCall(e, withResultParam = true)
    # c.instr(e.info, opcCopy, imm32 c.genType(e.typ))
  else:
    c.gen(e)

proc genAsgnToLocal(c: var TCtx, le, ri: CgNode, move: bool) =
  ## Generates and emits and assignment to a local variable. Local variables
  ## differ from other location in that their value can be stored directly
  ## in a register (although it doesn't have to).
  let dest = c.prc[le.local].slot
  if usesRegister(c, le.local):
    c.operand(ri)
    c.instr(le.info, opcPopLocal, imm32 dest)
  elif fitsRegister(le.typ):
    # the local is stored in-memory, a temporary register is needed
    c.getLocal(le.info, imm32 dest)
    c.operand(ri)
    c.instr(le.info, writeInstr(ri.typ))
  elif ri.kind in LvalueExprKinds:
    c.getLocal(le.info, imm32 dest)
    c.genLvalue(ri)
    if move:
      c.loadInt(le.info, toInt128 c.sizeof(le.typ))
      c.instr(le.info, opcMemCopy)
    else:
      c.instr(le.info, opcCopy, imm32 c.genType(le.typ))
  elif ri.kind in {cnkCheckedCall, cnkCall} and ri[0].kind != cnkMagic:
    c.getLocal(le.info, imm32 dest)
    c.genCall(ri, withResultParam=true)
  else:
    c.getLocal(le.info, imm32 dest)
    gen(c, ri)

proc hasUnsafe(e: CgNode): bool =
  case e.kind
  of cnkDeref:
    true
  of cnkDerefView:
    false
  of cnkTupleAccess, cnkArrayAccess, cnkFieldAccess:
    # TODO: treat sequence/string access as unsafe? The payload could have
    #       become corrupt
    hasUnsafe(e[0])
  of cnkLvalueConv, cnkObjDownConv, cnkObjUpConv:
    hasUnsafe(e.operand)
  of cnkGlobal, cnkLocal:
    false
  else:
    unreachable(e.kind)

proc check(c: var TCtx, info: TLineInfo, typ: PType) =
  # type checks are only a convenience feature. They're not necessary for safe
  # operation of the VM
  c.instr(info, opcCheck, imm32 c.genType(typ))

proc genAsgn(c: var TCtx; le, ri: CgNode, move: bool) =
  case le.kind
  of cnkArrayAccess:
    let typ = le[0].typ.skipTypes(abstractVar).kind
    case typ
    of tyString, tyCstring, tySequence:
      # the source value always fits into a register, so the `ld`
      # opcode doesn't matter
      c.operand(le[0])
      c.instr(le.info, opcLdInt32, imm32 8)
      # skip the capacity
      c.instr(le.info, opcAddImm, imm32 8)
    of tyOpenArray, tyVarargs:
      c.operand(le[0])
      c.instr(le.info, opcLdInt64, imm32 8)
    of tyArray, tyUncheckedArray:
      c.genLvalue(le[0])
    else:
      unreachable()

    c.genIndex(le[1], le[0].typ)
    c.instr(le.info, opcOffset, imm32 c.sizeof(le.typ))
    if hasUnsafe(le):
      c.check(le.info, ri.typ)
    putIntoLoc(c, ri, move)
  of cnkTupleAccess, cnkFieldAccess:
    c.genLvalue(le)
    if hasUnsafe(le):
      c.check(le.info, ri.typ)
    putIntoLoc(c, ri, move)
  of cnkDeref, cnkDerefView:
    # an assignment to a view's underlying location
    c.genLvalue(le.operand)
    if hasUnsafe(le):
      c.check(le.info, ri.typ)
    c.putIntoLoc(ri, move)
  of cnkLvalueConv, cnkObjDownConv, cnkObjUpConv:
    genAsgn(c, le.operand, ri, move)
  of cnkGlobal:
    c.instr(le.info, opcGetGlobal, imm32 le.global)
    putIntoLoc(c, ri, move)
  of cnkLocal:
    genAsgnToLocal(c, le, ri, move)
  else:
    unreachable(le.kind)

proc importcCond*(g: ModuleGraph; s: PSym): bool {.inline.} =
  ## return true to importc `s`, false to execute its body instead (refs #8405)
  if sfImportc in s.flags:
    if s.kind in routineKinds:
      return getBody(g, s).kind == nkEmpty

proc useGlobal(c: var TCtx, n: CgNode): int =
    ## Resolves the global identified by symbol node `n` to the ID that
    ## identifies it at run-time. If using the global is illegal (because
    ## it's an importc'ed variable, for example), an error is raised.
    let s = c.env[n.global]

    if importcCondVar(s) or c.graph.importcCond(s):
      # Using importc'ed symbols on the left or right side of an expression is
      # not allowed
      fail(n.info, vmGenDiagCannotImportc, sym = s)

    int n.global

proc genSym(c: var TCtx; n: CgNode; load = true) =
  ## Generates and emits the code for loading either the value or handle of
  ## the location named by symbol or local node `n` into the `dest` register.
  case n.kind
  of cnkConst:
    let pos = int c.env.dataFor(n.cnst)
    c.instr(n.info, opcGetGlobal, imm32 pos, imm8 1)
    if load and fitsRegister(n.typ):
      c.load(n.info, n.typ)

    discard genType(c, n.typ) # make sure the type exists
    # somewhat hack-y, but the orchestrator later queries the type of the data
    # (which might be a different PType that maps to the same VM type)
    discard genType(c, c.env[c.env[DataId pos][0].typ])
  of cnkGlobal:
    # a global location
    let pos = useGlobal(c, n)
    c.instr(n.info, opcGetGlobal, imm32 pos)

    if load and fitsRegister(n.typ):
      c.load(n.info, n.typ)
  of cnkLocal:
    c.getLocal(n.info, imm32 c.prc[n.local].slot)
    if not usesRegister(c, n.local) and fitsRegister(n.typ) and load:
      c.load(n.info, n.typ)
  else:
    unreachable()

proc genLvalue(c: var TCtx, n: CgNode) =
  ## Generates and emits the code for computing the handle of the location
  ## named by l-value expression `n`. If the expression names a location that
  ## is stored in a VM memory cell, `dest` will always store a handle --
  ## address-based views are dereferenced.
  ##
  ## Note that in the case of locals backed by registers, `dest` will store
  ## its value instead of a handle.
  case n.kind
  of cnkConst, cnkGlobal, cnkLocal:
    genSym(c, n, load=false)
  of cnkFieldAccess:
    c.genLvalue(n[0])
    c.addImm(n.info, toInt128 c.offsetof(n[0].typ, n[1]))
  of cnkArrayAccess:
    case n[0].typ.skipTypes(abstractVar).kind
    of tySequence, tyString, tyCstring:
      c.genLvalue(n[0])
      c.instr(n.info, opcLdInt64, imm32 8)
      c.instr(n.info, opcAddImm, imm32 8)
    of tyOpenArray, tyVarargs:
      c.genLvalue(n[0])
      c.instr(n.info, opcLdInt64, imm32 8)
    of tyArray, tyUncheckedArray:
      c.genLvalue(n[0])
    else:
      unreachable()

    c.genIndex(n[1], n[0].typ)
    # TODO: n sometimes has a lent/var type for forvars, figure out why
    c.instr(n.info, opcOffset, imm32 c.sizeof(elemType(n[0].typ.skipTypes(abstractVar))))
  of cnkTupleAccess:
    c.genLvalue(n[0])
    c.addImm(n.info, toInt128 c.offsetof(n[0].typ, n[1].intVal.int))
  of cnkLvalueConv:
    # lvalue conversion reaching here are only for distinct or tuple type
    # conversions, which are irrelevant to the VM
    genLvalue(c, n.operand)
  of cnkObjDownConv, cnkObjUpConv:
    # these conversions are *not* no-ops, as they produce a handle of different
    # type
    c.operand(n)
  of cnkDerefView:
    # simply load as a value
    c.operand(n.operand)
  of cnkDeref:
    c.operand(n.operand)
  else:
    unreachable(n.kind)

proc genDef(c: var TCtx; a: CgNode) =
        let
          s   = a[0].local
          typ = a[0].typ
        if true:
          if a[1].kind == cnkEmpty:
            # no initializer; only setup the register (and memory location,
            # if used)
            let reg = setSlot(c, s)
            if not usesRegister(c, s):
              # TODO: don't clear. Locals that require a default value should
              #       have an non-empty def
              c.instr(a.info, opcStackAlloc, imm32 c.genType(typ), imm8 1) # clear
              c.instr(a.info, opcPopLocal, imm32 reg)
          else:
            let reg = setSlot(c, s)
            # temporarily set the slot kind to something signaling that
            # initialization is in progress:
            var prev = slotUninit
            swap(prev, c.prc.regInfo[reg].kind)
            if not usesRegister(c, s):
              # XXX: clearing is unnecessary if the construction initializes
              #      everything
              c.instr(a.info, opcStackAlloc, imm32 c.genType(typ), imm8 1) # clear
              c.instr(a.info, opcPopLocal, imm32 reg)

            genAsgnToLocal(c, a[0], a[1], move=false)
            swap(prev, c.prc.regInfo[reg].kind)

proc genArrayConstr(c: var TCtx, n: CgNode) =
  if n.typ.skipTypes(abstractInst).kind == tySequence:
    c.dup(n.info)
    c.instr(n.info, opcLdImmInt, imm32 n.len)
    c.instr(n.info, opcLdImmInt, imm32 c.genType(n.typ))
    c.builtin(n.info, "__newseq", 3)
    # load the payload
    c.instr(n.info, opcLdInt64, imm32 8)
    c.instr(n.info, opcAddImm, imm32 8) # skip the capacity

  for x in n:
    c.dup(n.info) # duplicate the pointer
    putIntoLoc(c, x, move=false)
    # advance the pointer by one element
    c.addImm(x.info, toInt128 c.sizeof(x.typ))

  c.drop(n.info)

proc genSetConstr(c: var TCtx, n: CgNode) =
  let tmp = c.capture(n.info, slotAddress)
  if true:#not isEmpty(c.prc, dest):
    # zero the destination
    c.getLocal(n.info, tmp.slot)
    c.instr(n.info, opcLdImmInt, imm32 c.sizeof(n.typ))
    c.instr(n.info, opcMemClear)

  # XXX: since `first` stays the same across the loop, we could invert
  #      the loop around `genSetElem`'s logic...
  let first = firstOrd(c.config, n.typ.skipTypes(abstractInst))
  let size = c.sizeof(n.typ)
  for x in n.items:
    c.instr(x.info, opcGetLocal, tmp.slot)
    if x.kind == cnkRange:
      c.genSetElem(x[0], first)
      c.genSetElem(x[1], first)
      c.instr(n.info, opcInclRange, imm32 size)
    else:
      c.genSetElem(x, first)
      c.instr(n.info, opcIncl, imm32 size)

  c.freeTemp(tmp)

proc genObjConstr(c: var TCtx, n: CgNode) =
  let t = n.typ.skipTypes(abstractRange-{tyTypeDesc})
  let tmp = c.getTemp(slotAddress)
  if t.kind == tyObject:#not isEmpty(c.prc, obj):
    # reset the destination first, the construction might not initialize all
    # fields
    c.instr(n.info, opcSetLocal, imm32 tmp)
    c.instr(n.info, opcReset, imm32 c.genType(n.typ))
  else:
    c.instr(n.info, opcLdImmInt, imm32 c.types[VmTypeId c.genType(t)].b)
    c.builtin(n.info, "__newobj", 1)
    c.instr(n.info, opcPopLocal, imm32 tmp)

  for it in n.items:
    assert it.kind == cnkBinding and it[0].kind == cnkField
    c.instr(n.info, opcGetLocal, imm32 tmp)
    c.addImm(it.info, toInt128 c.offsetof(t, it[0]))
    putIntoLoc(c, it[1], move=false)

  if t.kind != tyObject:
    c.instr(n.info, opcGetLocal, imm32 tmp)
  c.freeTemp(tmp)

proc genTupleConstr(c: var TCtx, n: CgNode) =
  let tmp = c.capture(n.info, slotAddress)
  for i, it in n.pairs:
    c.getLocal(it.info, tmp.slot)
    c.addImm(it.info, toInt128 c.offsetof(n.typ, i))
    putIntoLoc(c, it, move=false)
  c.freeTemp(tmp)

proc genClosureConstr(c: var TCtx, n: CgNode) =
  c.dup(n.info)
  c.operand(n[0])
  c.instr(n.info, opcWrInt64, imm32 0)

  c.operand(n[1])
  c.instr(n.info, opcWrInt64, imm32 8)

proc binaryArith(c: var TCtx, e, x, y: CgNode,
                 intOp, floatOp: TOpcode) =
  ## Emits the instruction sequence for the binary operation `e` with opcode
  ## `op`. `x` and `y` are the operand expressions.
  c.binary(e.info, pick(e, intOp, floatOp), x, y)

proc gen(c: var TCtx; n: CgNode) =
  when defined(nimCompilerStacktraceHints):
    frameMsg c.config, n

  case n.kind
  of cnkProc:
    genProcLit(c, n)
  of cnkConst, cnkGlobal, cnkLocal:
    genSym(c, n)
  of cnkCall, cnkCheckedCall:
    let magic = getMagic(c.env, n)
    if magic != mNone:
      genMagic(c, n, magic)
    else:
      genCall(c, n)
  of cnkNeg:
    c.operand(n[0])
    c.instr(n.info, pick(n, opcNegInt, opcNegFloat))
  of cnkAdd: binaryArith(c, n, n[0], n[1], opcAddInt, opcAddFloat)
  of cnkSub: binaryArith(c, n, n[0], n[1], opcSubInt, opcSubFloat)
  of cnkMul: binaryArith(c, n, n[0], n[1], opcMulInt, opcMulFloat)
  of cnkDiv: binaryArith(c, n, n[0], n[1], opcDivInt, opcDivFloat)
  of cnkModI: binaryArith(c, n, n[0], n[1], opcModInt, opcModInt)
  of cnkIntLit, cnkUIntLit:
    c.loadInt(n.info, getInt(n))
  of cnkFloatLit, cnkStrLit: genLit(c, n)
  of cnkNilLit:
    if fitsRegister(n.typ):
      c.instr(n.info, opcLdImmInt, imm32 0)
    else:
      # assigning the nil literal is identical with resetting the
      # location
      c.instr(n.info, opcLdImmInt, imm32 c.sizeof(n.typ))
      c.instr(n.info, opcMemClear) # TODO: use reset where necessary
  of cnkAstLit:
    # turn into an integer value, the ``loadNimNode`` call it's passed to
    # will load the actual node
    c.loadInt(n.info, toInt128 ord(n.astLit))
  of cnkFieldAccess:
    if fitsRegister(n.typ):
      c.genLvalue(n)
      c.load(n.info, n.typ)
    else:
      c.genLvalue(n)
  of cnkArrayAccess:
    if fitsRegister(n.typ):
      case n[0].typ.skipTypes(abstractVar).kind
      of tySequence, tyString, tyCstring:
        c.genLvalue(n[0])
        c.instr(n.info, opcLdInt64, imm32 8)
        c.instr(n.info, opcAddImm, imm32 8)
      of tyOpenArray, tyVarargs:
        c.genLvalue(n[0])
        c.instr(n.info, opcLdInt64, imm32 8)
      of tyArray, tyUncheckedArray:
        c.genLvalue(n[0])
      else:
        unreachable()
      c.genIndex(n[1], n[0].typ)
      c.instr(n.info, opcOffset, imm32 c.sizeof(n.typ))
      c.load(n.info, n.typ)
    else:
      c.genLvalue(n)
  of cnkTupleAccess:
    if fitsRegister(n.typ):
      c.genLvalue(n)
      c.load(n.info, n.typ)
    else:
      c.genLvalue(n)
  of cnkToSlice:
    case n[0].typ.skipTypes(abstractVar).kind
    of tyArray:
      c.dup(n.info)
      # FIXME: multi evaluation, in case expressions are forwarded
      if n.len == 3:
        c.operand(n[2])
        c.operand(n[1])
        c.instr(n.info, opcSubInt)
        c.instr(n.info, opcAddImm, imm32 1)
      else:
        c.loadInt(n.info, c.config.lengthOrd(n[0].typ))
      c.instr(n.info, opcWrInt64)
      c.genLvalue(n[0])
      if n.len == 3:
        c.operand(n[2])
        c.instr(n.info, opcOffset, imm32 c.sizeof(elemType(n[0].typ)))
      c.instr(n.info, opcWrInt64, imm32 8)
    of tySequence, tyString:
      c.dup(n.info)
      c.genLvalue(n[0])
      let tmp = c.capture(n.info, slotAddress)
      if n.len == 3:
        c.operand(n[2])
        c.operand(n[1])
        c.instr(n.info, opcSubInt)
        c.instr(n.info, opcAddImm, imm32 1)
      else:
        c.getLocal(n.info, tmp.slot)
        c.rawLoad(n.info, opcLdInt64)
      c.instr(n.info, opcWrInt64)
      c.instr(n.info, opcGetLocal, tmp.slot)
      # ignore whether the pointer is nil or not
      c.instr(n.info, opcLdInt64, imm32 8)
      c.instr(n.info, opcAddImm, imm32 8) # skip to the first element
      if n.len == 3:
        c.operand(n[1])
        c.instr(n.info, opcOffset, imm32 c.sizeof(elemType(n[0].typ)))
      c.instr(n.info, opcWrInt64, imm32 8)
      c.freeTemp(tmp)
    of tyOpenArray, tyVarargs:
      if n.len == 1:
        c.operand(n[0])
        c.instr(n.info, opcCopy, imm32 c.genType(n.typ))
      else:
        missing("openArray-subslice")
    else:
      missing("openarray support")

  of cnkDeref, cnkDerefView:
    c.operand(n.operand)
    if fitsRegister(n.typ):
      c.load(n.info, n.typ)
  of cnkAddr:
    c.genLvalue(n.operand)
  of cnkHiddenAddr:
    c.genLvalue(n.operand)
    if hasUnsafe(n.operand):
      # typecheck the source handle
      c.check(n.info, n.operand.typ)
  of cnkHiddenConv, cnkConv:
    genConv(c, n, n.operand)
  of cnkLvalueConv:
    gen(c, n.operand)
  of cnkObjDownConv, cnkObjUpConv:
    c.genLvalue(n.operand)
  of cnkEmpty:
    discard
  of cnkArrayConstr: genArrayConstr(c, n)
  of cnkSetConstr: genSetConstr(c, n)
  of cnkObjConstr: genObjConstr(c, n)
  of cnkTupleConstr: genTupleConstr(c, n)
  of cnkClosureConstr: genClosureConstr(c, n)
  of cnkCast:
    genCast(c, n)
  else:
    unreachable(n.kind)

proc genStmt(c: var TCtx, n: CgNode) =
  case n.kind
  of cnkCall, cnkCheckedCall:
    let magic = getMagic(c.env, n)
    if magic != mNone:
      genMagic(c, n, magic)
    else:
      genCall(c, n)
  of cnkAsgn, cnkFastAsgn:
    # XXX: we can never safely move at the moment
    genAsgn(c, n[0], n[1], move = false)
  of cnkIfStmt:
    genIf(c, n)
  of cnkCaseStmt:
    genCase(c, n)
  of cnkRaiseStmt:
    genRaise(c, n)
  of cnkGotoStmt:
    genGoto(c, n)
  of cnkStmtList:
    # XXX: supported for a transition period (``cgir.merge`` creates nested
    #      statement lists)
    for x in n: genStmt(c, x)
  of cnkVoidStmt:
    gen(c, n[0])
    c.drop(n.info)
  of cnkContinueStmt:
    # marks the end of a finally section
    let
      blk {.cursor.} = c.prc.blocks[^1]
      control = c.controlReg(blk)
    # patch the ``opcFinally`` instruction:
    # c.patch(blk.start)
    c.instr(n.info, opcFinallyEnd, imm32 control)
    # now free the control register
    c.freeTemp(control)
    popBlock(c)
  of cnkJoinStmt:
    c.patch(n[0].label)
  of cnkLoopJoinStmt:
    # loops count as blocks too
    pushBlock(c):
      BlockInfo(kind: bkBlock, label: n[0].label, start: c.genLabel())
    c.prc.pastJoin = true # prevent instruction merging
  of cnkLoopStmt:
    c.jmpBack(n, c.prc.blocks[^1].start)
    popBlock(c)
  of cnkExcept:
    genExcept(c, n)
  of cnkFinally:
    genFinally(c, n)
  of cnkEnd:
    if c.prc.blocks[^1].kind == bkBlock:
      c.patch(c.prc.blocks[^1].start)
    popBlock(c)
  of cnkDef:
    genDef(c, n)
  of cnkAsmStmt, cnkEmitStmt:
    discard
  of cnkInvalid, cnkMagic, cnkRange, cnkBranch,
     cnkBinding, cnkLabel, cnkField, cnkToSlice,
     cnkResume, cnkTargetList, cnkLeave:
    unreachable(n.kind)
  else:
    unreachable(n.kind)

proc initProc(c: TCtx, owner: PSym, body: sink Body): BProc =
  ## `owner` is the procedure the body belongs to, or nil, if its something
  ## standalone.
  result = BProc(sym: owner, body: body)
  result.locals.synchronize(result.body.locals)

  # analyse what locals require indirections:
  analyseIfAddressTaken(result.body.code, result)

proc genStmt*(c: var TCtx; body: sink Body): Result[int, VmGenDiag] =
  c.prc = initProc(c, nil, body)
  let n = c.prc.body.code

  try:
    setupEh(c)
    c.genStmt(n)
  except VmGenError as e:
    return typeof(result).err(move e.diag)

  if c.prc.body[resultId].typ != mirtypes.VoidType:
    # the body has a result, emit a return. Always do this, even if the
    # local is an address
    c.getLocal(n.info, imm32 c.prc[resultId].slot)
    c.instr(n.info, opcRet)

  result = typeof(result).ok(c.prc.regInfo.len)


proc genParams(env: MirEnv, prc: var BProc; signature: PType) =
  ## Allocates the registers for the parameters and associates them with the
  ## corresponding locs.
  let
    params = signature.n
    isClosure = signature.callConv == ccClosure

  # closure procedures have an additional, hidden parameter
  prc.regInfo.newSeq(params.len + ord(isClosure))

  for i, it in prc.regInfo.mpairs:
    it = RegInfo(inUse: true, kind: getSlotKind(env.types[prc.body[LocalId i].typ]))
    prc[LocalId i].slot = LocalIndex i

proc finalJumpTarget(c: var TCtx; pc, diff: int) =
  let oldInstr = c.code[pc]
  # opcode and regA stay the same:
  missing("patch")

#[
proc optimizeJumps(c: var TCtx; start: int) =
  const maxIterations = 10
  for i in start..<c.code.len:
    let opc = c.code[i].opcode
    case opc
    of opcTJmp, opcFJmp:
      var reg = c.code[i].regA
      var d = i + c.code[i].jmpDiff
      for iters in countdown(maxIterations, 0):
        case c.code[d].opcode
        of opcJmp:
          d += c.code[d].jmpDiff
        of opcTJmp, opcFJmp:
          if c.code[d].regA != reg: break
          # tjmp x, 23
          # ...
          # tjmp x, 12
          # -- we know 'x' is true, and so can jump to 12+13:
          if c.code[d].opcode == opc:
            d += c.code[d].jmpDiff
          else:
            # tjmp x, 23
            # fjmp x, 22
            # We know 'x' is true so skip to the next instruction:
            d += 1
        else: break
      if d != i + c.code[i].jmpDiff:
        c.finalJumpTarget(i, d - i)
    of opcJmp, opcJmpBack:
      var d = i + c.code[i].jmpDiff
      var iters = maxIterations
      while c.code[d].opcode == opcJmp and iters > 0:
        d += c.code[d].jmpDiff
        dec iters
      if c.code[d].opcode == opcRet:
        # optimize 'jmp to ret' to 'ret' here
        c.code[i] = c.code[d]
      elif d != i + c.code[i].jmpDiff:
        c.finalJumpTarget(i, d - i)
    else: discard
]#

proc transitionToLocation(c: var TCtx, info: TLineInfo, typ: PType, loc: int32) =
  ## Transitions the register `reg`, which is expected to store a value of
  ## type `typ` directly, to store an owning handle to a location instead.
  ## The location is initialized with the original value. `info` is only used
  ## for providing line information.
  assert fitsRegister(typ)
  c.instr(info, opcStackAlloc, imm32 c.genType(typ))
  c.instr(info, opcSetLocal, imm32 loc)
  c.instr(info, opcSwap)
  c.instr(info, writeInstr(typ))

proc prepareParameters(c: var TCtx, info: CgNode) =
  ## Prepares immutable parameters backed by registers for having their address
  ## taken. If an immutable parameter has its address taken, it is transitioned
  ## to a VM memory location at the start of the procedure.
  let typ = c.prc.sym.routineSignature # the procedure's type

  if ccClosure == typ.callConv:
    c.instr(info.info, opcPopLocal, imm32 c.prc[LocalId(typ.len)].slot)

  # commit the stack operands to locals. They're stored in reverse
  for i in countdown(typ.len-1, 1):
    if typ[i].kind != tyStatic:
      if fitsRegister(typ[i]) and c.prc[LocalId(i)].isIndirect:
        transitionToLocation(c, info.info, typ[i], imm32 i)
      else:
        c.instr(info.info, opcPopLocal, imm32 i)

  if not typ[0].isEmptyType() and not fitsRegister(typ[0]):
    # the result address is passed as a parameter
    c.instr(info.info, opcPopLocal, imm32 c.prc[resultId].slot)

proc genProcBody(c: var TCtx): int =
    let
      s    = c.prc.sym
      body = c.prc.body.code
      info = body.info

    genParams(c.env, c.prc, s.routineSignature)

    prepareParameters(c, body)

    # setup the result register, if necessary. Watch out for macros! Their
    # result register is setup at the start of macro evaluation
    # XXX: initializing the ``result`` of a macro should be handled through
    #      inserting the necessary code either in ``sem` or here
    let rt = c.env[c.prc.body[resultId].typ]
    if not isEmptyType(rt) and fitsRegister(rt):
      # initialize the register holding the result
      if not usesRegister(c, resultId):
        c.instr(info, opcStackAlloc, imm32 c.sizeof(rt))
        c.instr(info, opcPopLocal, imm32 c.prc[resultId].slot)


    elif not isEmptyType(rt):
      # reset the result variable
      c.getLocal(info, imm32 0)
      # XXX: inserting the reset needs to happen via a MIR pass
      c.instr(info, opcLdImmInt, imm32 c.sizeof(rt))
      c.instr(info, opcMemClear) # TODO: use reset where necessary

    setupEh(c)
    genStmt(c, body)

    # generate the final 'return' statement:
    writeBackResult(c, info)
    c.instr(info, opcRet)

    if c.prc.overflows.len > 0:
      for it in c.prc.overflows:
        c.patch(it)
      c.instr(info, opcRaise)

    result = c.prc.regInfo.len

proc genProc*(c: var TCtx; s: PSym, body: sink Body): VmGenResult =
  # thanks to the jmp we can add top level statements easily and also nest
  # procs easily:
  let
    start = c.code.len+1 # skip the jump instruction
    procStart = c.xjmp(body.code, opcJmp, 0)

  c.prc = initProc(c, s, body)
  let regCount = tryOrReturn:
    c.genProcBody()

  c.patch(procStart)
  # c.optimizeJumps(start)

  var locs = newSeq[AtomKind](regCount)
  for i in 0..<locs.len:
    locs[i] = case c.prc.regInfo[i].kind
      of slotAddress: akInt
      of slotInt:     akInt
      of slotRef:     akForeign
      of slotFloat:   akFloat
      of slotUninit: unreachable()

  result = VmGenResult.ok:
    (start: start, locals: locs)

func vmGenDiagToAstDiagVmGenError*(diag: VmGenDiag): AstDiagVmGenError {.inline.} =
  let kind =
    case diag.kind
    of vmGenDiagTooManyRegistersRequired: adVmGenTooManyRegistersRequired
    of vmGenDiagNotUnused: adVmGenNotUnused
    of vmGenDiagCannotEvaluateAtComptime: adVmGenCannotEvaluateAtComptime
    of vmGenDiagMissingImportcCompleteStruct: adVmGenMissingImportcCompleteStruct
    of vmGenDiagCodeGenUnhandledMagic: adVmGenCodeGenUnhandledMagic
    of vmGenDiagCannotImportc: adVmGenCannotImportc
    of vmGenDiagTooLargeOffset: adVmGenTooLargeOffset
    of vmGenDiagCannotCallMethod: adVmGenCannotCallMethod
    of vmGenDiagCannotCast: adVmGenCannotCast

  {.cast(uncheckedAssign).}: # discriminants on both sides lead to saddness
    result =
      case diag.kind
      of vmGenDiagCannotImportc,
          vmGenDiagTooLargeOffset,
          vmGenDiagCannotCallMethod:
        AstDiagVmGenError(
          kind: kind,
          sym: diag.sym)
      of vmGenDiagCannotCast:
        AstDiagVmGenError(
          kind: kind,
          formalType: diag.typeMismatch.formalType,
          actualType: diag.typeMismatch.actualType)
      of vmGenDiagMissingImportcCompleteStruct,
          vmGenDiagCodeGenUnhandledMagic:
        AstDiagVmGenError(
          kind: kind,
          magic: diag.magic)
      of vmGenDiagNotUnused,
          vmGenDiagCannotEvaluateAtComptime:
        AstDiagVmGenError(
          kind: kind,
          ast: diag.ast)
      of vmGenDiagTooManyRegistersRequired:
        AstDiagVmGenError(kind: kind)
