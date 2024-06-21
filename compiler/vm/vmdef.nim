#
#
#           The Nim Compiler
#        (c) Copyright 2013 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module contains the type definitions for the new evaluation engine.
## An instruction is 1-3 int32s in memory, it is a register based VM.

import
  std/[
    intsets,
    tables
  ],
  compiler/ast/[
    ast,
    idents,
    lineinfos,
  ],
  compiler/modules/[
    modulegraphs
  ],
  compiler/front/[
    options,
  ],
  compiler/utils/[
    idioms
  ],
  compiler/vm/[
    vmalloc,
    vmtypes
  ]

import std/options as std_options

import vm_enums
export vm_enums

type TInstrType* = uint64

const
  regOBits = 8 # Opcode
  regABits = 32
  regBBits = 16
  regCBits = 8

# Calculate register shifts, masks and ranges

const
  regOShift* = 0.TInstrType
  regAShift* = (regOShift + regOBits)
  regBShift* = (regAShift + regABits)
  regCShift* = (regBShift + regBBits)
  regBxShift* = (regAShift + regABits)

  regOMask*  = ((1.TInstrType shl regOBits) - 1)
  regAMask*  = ((1.TInstrType shl regABits) - 1)
  regBMask*  = ((1.TInstrType shl regBBits) - 1)
  regCMask*  = ((1.TInstrType shl regCBits) - 1)

type
  PrgCtr* = int  ## Program Counter, aliased as it's self-documenting and supports
                 ## changing the type in the future (distinct/width)

  TInstr* = distinct TInstrType

  TEvalMode* = enum           ## reason for evaluation
    emRepl,                   ## evaluate because in REPL mode
    emConst,                  ## evaluate for 'const' according to spec
    emOptimize,               ## evaluate for optimization purposes (same as
                              ## emConst?)
    emStaticExpr,             ## evaluate for enforced compile time eval
                              ## ('static' context)
    emStaticStmt              ## 'static' as an expression
    emStandalone              ## standalone execution separate from
                              ## code-generation

  TSandboxFlag* = enum        ## what the evaluation engine should allow
    allowCast,                ## allow unsafe language feature: 'cast'
    allowInfiniteLoops        ## allow endless loops
  TSandboxFlags* = set[TSandboxFlag]

  CodeInfo* = tuple
    # TODO: remove; shouldn't be needed
    start: int ## The position where the bytecode starts
    locals: seq[AtomKind] ## The maximum number of registers required to run the code

  CallableKind* = enum # TODO: rename
    ckStub     ## a stub
    ckDefault  ## a normal procedure
    ckCallback ## invokes a callback

  VmFunctionPtr* = distinct int

  ProcEntry* = object
    ## A procedure table entry. Stores the runtime-relevant information for a
    ## procedure callable within the VM.
    sym*: PSym # TODO: don't store the symbol here, store it in a separate debug table
    typ*: VmTypeId
    isClosure*: bool     ## whether the closure calling convention is used

    case kind*: CallableKind
    of ckStub:
      discard
    of ckDefault:
      start*: int ## the code position where the function starts
      # TODO: use a separate, standalone storage
      locals*: seq[AtomKind]
      eh*: HOslice[uint32]
    of ckCallback:
      cbOffset*: int ## the index into the callback list

  VmConstant* = object
    typ*: AtomKind
    val*: StackValue

  CallbackExitCode* = enum
    cecNothing # success; nothing is returned
    cecValue   # success; a value is returned
    cecRaise   # an exception is raised
    cecError   # memory error. The VM yields

  CallbackResult* = tuple[code: CallbackExitCode, value: StackValue]

  VmCallback* = proc (env: var VmEnv, args: openArray[StackValue], cl: RootRef): (CallbackExitCode, StackValue) {.nimcall, raises: [].}

  LinkIndex* = uint32
    ## Identifies a linker-relevant entity. There are three namespaces, one
    ## for procedures, one for globals, and one for constants -- which
    ## namespace an index is part of is stored separately.

  FunctionIndex* = distinct int # TODO: this needs to be a uint32

  CodeGenFlag* = enum
    cgfAllowMeta ## If not present, type or other meta expressions are
                 ## disallowed in imperative contexts and code-gen for meta
                 ## function arguments (e.g. `typedesc`) is suppressed

  VmGenDiagKind* = enum
    # has no extra data
    vmGenDiagTooManyRegistersRequired
    # has ast data
    vmGenDiagNotUnused
    vmGenDiagCannotEvaluateAtComptime
    # has magic data
    vmGenDiagMissingImportcCompleteStruct
    vmGenDiagCodeGenUnhandledMagic
    # has sym data
    vmGenDiagCannotImportc
    vmGenDiagTooLargeOffset
    vmGenDiagCannotCallMethod
    # has type mismatch data
    vmGenDiagCannotCast

  VmGenDiagKindAstRelated* =
    range[vmGenDiagNotUnused..vmGenDiagCannotEvaluateAtComptime]
    # TODO: this is a somewhat silly type, the range allows creating type safe
    #       diag construction functions -- see: `vmgen.fail`

  VmGenDiagKindSymRelated* =
    range[vmGenDiagCannotImportc..vmGenDiagCannotCallMethod]
    # TODO: this is a somewhat silly type, the range allows creating type safe
    #       diag construction functions -- see: `vmgen.fail`

  VmGenDiagKindMagicRelated* =
    range[vmGenDiagMissingImportcCompleteStruct..vmGenDiagCodeGenUnhandledMagic]
    # TODO: this is a somewhat silly type, the range allows creating type safe
    #       diag construction functions -- see: `vmgen.fail`

  VmTypeMismatch* = object
    actualType*, formalType*: PType

  VmGenDiag* = object
    ## `Diag`nostic data from VM Gen, mostly errors
    # TODO: rework fields and enum order so they form sensible categories,
    #       introducing overlapping field types across variants is fine.
    location*: TLineInfo        ## diagnostic location
    instLoc*: InstantiationInfo ## instantiation in VM Gen's source
    case kind*: VmGenDiagKind
      of vmGenDiagCannotImportc,
          vmGenDiagTooLargeOffset,
          vmGenDiagCannotCallMethod:
        sym*: PSym
      of vmGenDiagCannotCast:
        typeMismatch*: VmTypeMismatch
      of vmGenDiagMissingImportcCompleteStruct,
          vmGenDiagCodeGenUnhandledMagic:
        magic*: TMagic
      of vmGenDiagNotUnused,
          vmGenDiagCannotEvaluateAtComptime:
        ast*: PNode
      of vmGenDiagTooManyRegistersRequired:
        discard

  VmEventKind* = enum
    vmEvtOpcParseExpectedExpression
    vmEvtUserError
    vmEvtUnhandledException
    vmEvtCannotCast
    vmEvtCannotModifyTypechecked
    vmEvtNilAccess
    vmEvtAccessOutOfBounds
    vmEvtAccessTypeMismatch
    vmEvtAccessNoLocation
    vmEvtErrInternal
    vmEvtIndexError
    vmEvtOutOfRange
    vmEvtOverOrUnderflow
    vmEvtDivisionByConstZero
    vmEvtArgNodeNotASymbol
    vmEvtNodeNotASymbol
    vmEvtNodeNotAProcSymbol
    vmEvtIllegalConv
    vmEvtIllegalConvFromXToY
    vmEvtMissingCacheKey
    vmEvtCacheKeyAlreadyExists
    vmEvtFieldNotFound
    vmEvtNotAField
    vmEvtFieldUnavailable
    vmEvtCannotCreateNode
    vmEvtCannotSetChild
    vmEvtCannotAddChild
    vmEvtCannotGetChild
    vmEvtNoType
    vmEvtTooManyIterations

  VmEventKindAccessError* = range[vmEvtAccessOutOfBounds .. vmEvtAccessNoLocation]

  VmEvent* = object
    ## Event data from a VM instance, mostly errors
    instLoc*: InstantiationInfo    ## instantiation in VM's source
    case kind*: VmEventKind
      of vmEvtUserError:
        errLoc*: TLineInfo
        errMsg*: string
      of vmEvtArgNodeNotASymbol:
        callName*: string
        argAst*: PNode
        argPos*: int
      of vmEvtCannotCast, vmEvtIllegalConvFromXToY:
        typeMismatch*: VmTypeMismatch
      of vmEvtIndexError:
        indexSpec*: tuple[usedIdx, minIdx, maxIdx: Int128]
      of vmEvtErrInternal, vmEvtNilAccess, vmEvtIllegalConv,
          vmEvtFieldUnavailable, vmEvtFieldNotFound,
          vmEvtCacheKeyAlreadyExists, vmEvtMissingCacheKey,
          vmEvtCannotCreateNode:
        msg*: string
      of vmEvtCannotSetChild, vmEvtCannotAddChild, vmEvtCannotGetChild,
         vmEvtNoType, vmEvtNodeNotASymbol:
        ast*: PNode
      of vmEvtUnhandledException:
        exc*: PNode
        trace*: VmRawStackTrace
      of vmEvtNotAField:
        sym*: PSym
      else:
        discard

  TraceHandler* = proc(c: VmEnv, pc: PrgCtr): void
  # XXX: probably better done via a yield. Maybe tracing in its current form
  #      should be removed as a whole... It has per-instruction overhead, even
  #      if not used

  VmStackTrace* = object
    # xxx: if possible remove `currentExceptionA` and `currentExceptionB` as
    #      they're not queried.
    currentExceptionA*, currentExceptionB*: PNode
    stacktrace*: seq[tuple[sym: PSym, location: TLineInfo]]
    skipped*: int

  VmRawStackTrace* = seq[tuple[sym: PSym, pc: PrgCtr]]

  HandlerTableEntry* = tuple
    offset: uint32 ## instruction offset
    instr:  uint32 ## position of the EH instruction to spawn a thread with

  EhOpcode* = enum
    ehoExcept
      ## unconditional exception handler
    ehoExceptWithFilter
      ## conditionl exception handler. If the exception is a subtype or equal
      ## to the specified type, the handler is entered
    ehoFinally
      ## enter the ``finally`` handler
    ehoNext
      ## relative jump to another instruction
    ehoLeave
      ## abort the parent thread
    ehoEnd
      ## ends the thread without treating the exception as handled

  EhInstr* = tuple
    ## Exception handling instruction. 8-byte in size.
    opcode: EhOpcode
    a: uint16 ## meaning depends on the opcode
    b: uint32 ## meaning depends on the opcode

  StackValue* = distinct BiggestUInt
    # TODO: rename to just Value; it's not only used for stack operands

  VmEnv* = object
    ## The total VM environment, storing all data needed across threads. An
    ## instance of this type represents a full VM instance.
    code*: seq[TInstr]
    debug*: seq[TLineInfo]  # line info for every instruction; kept separate
                            # to not slow down interpretation
    ehTable*: seq[HandlerTableEntry]
      ## stores the instruction-to-EH mappings. Used to look up the EH
      ## instruction to start exception handling with in case of a normal
      ## instruction raising
    ehCode*: seq[EhInstr]
      ## stores the instructions for the exception handling (EH) mechanism

    globals*: array[2, seq[tuple[typ: VmTypeId, val: StackValue]]]
    constants*: seq[VmConstant]
    procs*: seq[ProcEntry]
      ## the function table. Contains an entry ## for each procedure known to
      ## the VM. Indexed by `FunctionIndex`
    types*: VmTypeEnv

    allocator*: VmAllocator
    # XXX: separating the allocator for the environment would makes sense
    #      from an architectural perspective, as it's the only data modified
    #      by the VM during execution. Doing so would also make `VmEnv`
    #      copyable!

    callbacks*: seq[VmCallback]
      ## registered callbacks; associated with imported functions

    features*: TSandboxFlags # XXX: maybe obsolete?
    vmTraceHandler*: TraceHandler ## handle trace output from an executing vm

  TCtx* = VmEnv

  TStackFrame* = object
    # TODO: remove
    prc*: FunctionIndex                 # current prc; proc that is evaluated
    start*: int
      ## position in the thread's register sequence where the registers for
      ## the frame start
    eh*: HOslice[int]
      ## points to the active list of instruction-to-EH mappings
    baseOffset*: PrgCtr
      ## the instruction that all offsets in the instruction-to-EH list are
      ## relative to. Only valid when `eh` is not empty

    comesFrom*: int

  ProfileInfo* = object
    ## Profiler data for a single procedure.
    time*: float ## the time spent on executing instructions (inclusive)
    count*: int  ## the number of instructions executed (exclusive)

  Profiler* = object
    # XXX: move this type to the ``vmprofiler`` module once possible
    enabled*: bool ## whether profiling is enabled
    tEnter*: float ## the point-in-time when the active measurment started

    data*: Table[FunctionIndex, ProfileInfo]
      ## maps the symbol of a procedure to the associated data gathered by the
      ## profiler

func `==`*(a, b: FunctionIndex): bool {.borrow.}

func toFuncPtr*(x: FunctionIndex): VmFunctionPtr =
  VmFunctionPtr(int(x) + 1)

func toFuncIndex*(x: VmFunctionPtr): FunctionIndex =
  assert int(x) > 0 # the caller needs to make sure that x != 0
  FunctionIndex(int(x) - 1)

template isNil*(x: VmFunctionPtr): bool = int(x) == 0

proc defaultTracer(c: VmEnv, pc: PrgCtr) =
  echo "default echo tracer ", pc

proc initCtx*(tracer: TraceHandler = defaultTracer): VmEnv =
  result = VmEnv(
    code: @[],
    debug: @[],
    constants: @[],
    vmtraceHandler: tracer
  )
  result.allocator = initAllocator(1024 * 1024 * 2000)
  # result.profiler.enabled = optProfileVM in g.config.globalOptions

template opcode*(x: TInstr): Opcode = Opcode(x.TInstrType shr regOShift and regOMask)
template imm32*(x: TInstr): int32 = cast[int32](x.TInstrType shr regAShift and regAMask)
template imm32_16*(x: TInstr): untyped =
  (cast[int32](x.TInstrType shr regAShift and regAMask), cast[int16](x.TInstrType shr regBShift and regBMask))
template imm32_8*(x: TInstr): untyped =
  (cast[int32](x.TInstrType shr regAShift and regAMask), cast[int8](x.TInstrType shr regBShift and regBMask))
template imm8*(x: TInstr): untyped = cast[int8](x.TInstrType shr regBShift and 0xFF)

template uintVal*(x: StackValue): untyped = cast[BiggestUInt](x)
template intVal*(x: StackValue): untyped = cast[BiggestInt](x)
template floatVal*(x: StackValue): untyped = cast[BiggestFloat](x)
template addrVal*(x: StackValue): untyped = cast[VirtualAddr](x)

proc `$`*(x: StackValue): string =
  "(uint: " & $x.uintVal & " int: " & $x.intVal & " float: " & $x.floatVal & ")"

template subView*[T](x: openArray[T], off, len): untyped =
  x.toOpenArray(off, int(uint(off) + uint(len) - 1))

template subView*[T](x: openArray[T], off): untyped =
  x.toOpenArray(int off, x.high)

# TODO: move `overlap` and its tests somewhere else
func overlap*(a, b: int, aLen, bLen: Natural): bool =
  ## Tests if the ranges `[a, a+aLen)` and `[b, b+bLen)` have elements
  ## in common
  let ar = a + aLen - 1
  let br = b + bLen - 1
  let x = ar - b
  let y = br - a
  if x >= 0 and y >= 0:
    return true

func overlap*(a, b: pointer, aLen, bLen: Natural): bool =
  ## Test if the memory regions overlap
  overlap(cast[int](a), cast[int](b), aLen, bLen)

static:
  func test(a, al, b, bl: int, invert = false) =
    if not invert:
      assert overlap(a, b, al, bl)
      assert overlap(b, a, bl, al)
    else:
      assert not overlap(a, b, al, bl)
      assert not overlap(b, a, bl, al)

  test(0, 10, 0, 10) # same range
  test(0, 5, 4, 1) # sharing a single element 1
  test(0, 5, 4, 6) # sharing a single element 2
  test(0, 5, 5, 5, true) # disjoint
  test(0, 10, 2, 6) # a contains b

# TODO: move `safeCopyMem` and `safeZeroMem` somewhere else

func safeCopyMem*(dest: var openArray[byte|char], src: openArray[byte|char], numBytes: Natural) {.inline.} =
  # TODO: Turn the asserts into range checks instead
  assert numBytes <= dest.len
  assert numBytes <= src.len, $numBytes & ", " & $src.len
  if numBytes > 0:
    # Calling `safeCopyMem` with empty src/dest would erroneously raise without the > 0 check
    assert not overlap(addr dest[0], unsafeAddr src[0], dest.len, src.len)
    copyMem(addr dest[0], unsafeAddr src[0], numBytes)

func safeCopyMemSrc*(dest: var openArray[byte], src: openArray[byte]) {.inline.} =
  # TODO: turn assert into a range check
  assert src.len <= dest.len
  if src.len > 0:
    assert not overlap(addr dest[0], unsafeAddr src[0], dest.len, src.len)
    copyMem(addr dest[0], unsafeAddr src[0], src.len)

func safeZeroMem*(dest: var openArray[byte], numBytes: Natural) =
  assert numBytes <= dest.len
  if numBytes > 0:
    # Calling `safeZeroMem` with empty `dest` would erroneously raise without this check
    zeroMem(addr dest[0], numBytes)
