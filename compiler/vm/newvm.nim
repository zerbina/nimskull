
import std/[options, strutils]
import compiler/vm/[vmdef, vmerrors, vmcompilerserdes, vmalloc, vmtypes, vmobjects, vmchecks]
import compiler/utils/[idioms, bitsets]
import experimental/results

import compiler/ast/[ast_types, lineinfos, ast]

type

  YieldReasonKind* = enum
    yrkDone
      ## execution is done. There is no more code to execute
    yrkError
      ## an error occurred. No clear distinction between fatal (the thread
      ## must not be resumed) and non-fatal (the thread may be resumed) is
      ## made yet, so all errors should be treated as fatal
    yrkUnhandledException
      ## an exception was raised an not handled. Execution *cannot* resume
      ## after this event
    yrkMissingProcedure
      ## a procedure stub was called. The stub has to be resolved before
      ## continuing execution
    yrkUser
      ## some user-specified yield reason. Usually used for implementing
      ## syscalls

  YieldReason* = object
    ## The result of a single execution step (i.e. a call to ``execute``)
    case kind*: YieldReasonKind:
    of yrkDone:
      typ*: VmTypeId
      reg*: Option[StackValue] ## the register that holds the result, or
                              ## 'none', if there is no result
    of yrkError:
      error*: VmEvent
    of yrkUnhandledException:
      exc*: VirtualAddr
    of yrkMissingProcedure:
      entry*: FunctionIndex   ## the entry of the procedure that is a stub
    of yrkUser:
      reason*: int
      args*: int

  Frame* = object
    prc*: int
    start*: int # first local
    comesFrom: PrgCtr # caller PC
    ctx: StackInfo
    # sp: int
    fp: int

  VmThread* = object
    stack*: seq[StackValue]
    locals*: seq[StackValue]
    frames*: seq[Frame]
    # XXX: the above three should not be exported
    free: seq[uint32]

    pc*: PrgCtr

    # state related to exception handling:
    currentException: StackValue
      ## the exception ref that's returned when querying the current exception
    ehStack: seq[tuple[ex: StackValue, pc: uint32]]
      ## the stack of currently executed EH threads. A stack is needed since
      ## exceptions can be raised while another exception is in flight

const
  fromEhBit = 0x8000_0000_0000_0000'u64

proc createStackTrace*(
    c:          TCtx,
    thread:     VmThread,
    recursionLimit: int = 100
  ): VmStackTrace =
  assert thread.frames.len > 0

  result = VmStackTrace()

  block:
    var count = 0
    var pc = thread.pc
    # create the stacktrace entries:
    for i in countdown(thread.frames.high, 0):
      let f {.cursor.} = thread.frames[i]

      if count < recursionLimit - 1 or i == 0:
        # The `i == 0` is to make sure that we're always including the
        # bottom of the stack (the entry function) in the trace

        # Since we're walking the stack from top to bottom,
        # the elements are added to the trace in reverse order
        # (the most recent function is first in the list, not last).
        # This needs to be accounted for by the actual reporting logic
        result.stacktrace.add((sym: c.procs[f.prc].sym, location: c.debug[pc]))

      pc = f.comesFrom
      inc count

    if count > recursionLimit:
      result.skipped = count - recursionLimit

  assert result.stacktrace.len() <= recursionLimit # post condition check

proc findEh(c: TCtx, t: VmThread, at: PrgCtr, frame: int
           ): Option[(int, uint32)] =
  ## Searches for the EH instruction that is associated with `at`. If none is
  ## found on the current stack frame, the caller's call instruction is
  ## inspected, then the caller of the caller, etc.
  ##
  ## On success, the EH instruction position and the stack frame the handler
  ## is attached to are returned.
  var
    pc = at
    frame = frame

  while frame >= 0:
    let
      handlers = c.procs[t.frames[frame].prc].eh
      offset = uint32(pc - c.procs[t.frames[frame].prc].start)

    # search for the instruction's asscoiated exception handler:
    for i in handlers.items:
      if c.ehTable[i].offset == offset:
        return some (frame, c.ehTable[i].instr)

    # no handler was found, try the above frame
    pc = t.frames[frame].comesFrom
    dec frame

  # no handler exists

proc decodeControl(x: BiggestUInt): tuple[fromEh: bool, val: uint32] =
  result.fromEh = bool(x shr 63)
  result.val = uint32(x)

proc runEh(t: var VmThread, c: TCtx): Result[PrgCtr, StackValue] {.raises: [].} =
  ## Executes the active EH thread. Returns either the bytecode position to
  ## resume main execution at, or the uncaught exception.
  ##
  ## This implements the VM-in-VM for executing the EH instructions.
  template tos: untyped =
    # top-of-stack
    t.ehStack[^1]

  while true:
    let instr = c.ehCode[tos.pc]
    # already move to the next instruction
    inc tos.pc

    template yieldControl() =
      t.currentException = tos.ex
      result.initSuccess(instr.b.PrgCtr)
      return

    case instr.opcode
    of ehoExcept, ehoFinally:
      # enter exception handler
      yieldControl()
    of ehoExceptWithFilter:
      missing("exception filter")
    of ehoNext:
      tos.pc += instr.b - 1 # account for the ``inc`` above
    of ehoLeave:
      case instr.a
      of 0:
        # discard the parent thread
        swap(tos, t.ehStack[^2])
        t.ehStack.setLen(t.ehStack.len - 1)
      of 1:
        # discard the parent thread if it's associated with the provided
        # control register
        let (fromEh, _) = decodeControl(t.locals[t.frames[^1].start + instr.b.int].uintVal)
        if fromEh:
          swap(tos, t.ehStack[^2])
          t.ehStack.setLen(t.ehStack.len - 1)
      else:
        unreachable()
    of ehoEnd:
      # terminate the thread and return the unhandled exception
      result.initFailure(move t.ehStack[^1].ex)
      t.ehStack.setLen(t.ehStack.len - 1)
      break

proc resumeEh(c: TCtx, t: var VmThread,
              frame: int): Result[PrgCtr, StackValue] =
  ## Continues raising the exception from the top-most EH thread. If exception
  ## handling code is found, unwinds the stack till where the handler is
  ## located and returns the program counter where to resume. Otherwise
  ## returns the unhandled exception.
  var frame = frame
  while true:
    let r = runEh(t, c)
    if r.isOk:
      # an exception handler or finalizer is entered. Unwind to the target
      # frame:
      if frame < t.frames.len - 1:
        t.locals.setLen(t.frames[frame+1].start)
        t.frames.setLen(frame + 1)
      # return control to the VM:
      return r
    elif frame == 0:
      # no more stack frames to unwind -> the exception is unhandled
      return r
    else:
      # exception was not handled on the current frame, try the frame above
      let pos = findEh(c, t, t.frames[frame].comesFrom, frame)
      if pos.isSome:
        # EH code exists in a frame above. Run it
        frame = pos.get()[0] # update to the frame the EH code is part of
        t.ehStack.add (r.takeErr(), pos.get()[1])
      else:
        return r

proc opRaise(c: TCtx, t: var VmThread, at: PrgCtr,
             ex: StackValue): Result[PrgCtr, StackValue] =
  ## Searches for an exception handler for the instruction at `at`. If one is
  ## found, the stack is unwound till the frame the handler is in and the
  ## position where to resume is returned. If there no handler is found, `ex`
  ## is returned.
  let pos = findEh(c, t, at, t.frames.high)
  if pos.isSome:
    # spawn and run the EH thread:
    t.ehStack.add (ex, pos.get()[1])
    result = resumeEh(c, t, pos.get()[0])
  else:
    # no exception handler exists:
    result.initFailure(ex)

# the validation layer makes sure that all operations are legal, we don't need
# any runtime checks! (as long as the execution loop is implemented correctly,
# of course)
when not defined(debug):
  {.push checks: off.}

proc gc(c: var TCtx, stack: seq[StackValue], t: VmThread) =
  ## Garbage collections for foreign references. Classic deferred refcounting
  ## is used.
  var keepAlive: seq[ForeignRef]
  var lp = 0
  for frame in t.frames.items:
    for i in 0..<c.procs[frame.prc.int].locals.len:
      if c.procs[frame.prc.int].locals[i] == akForeign:
        let r = cast[ForeignRef](t.locals[lp + i])
        if check(c.allocator, r):
          # keep alive for the duration of garbage collection
          c.allocator.incRef(r)
          keepAlive.add r

    lp += c.procs[frame.prc.int].locals.len

  # scan the operand stack for things looking like foreign references
  for it in stack.items:
    let r = ForeignRef(it)
    if check(c.allocator, r):
      c.allocator.incRef(r)
      keepAlive.add r

  for it in c.allocator.zct.items:
    c.allocator.cleanup(it)

  c.allocator.zct.setLen(0)

  # decrement the locally referenced cells again
  for it in keepAlive.items:
    c.allocator.decRef(it)

proc run*(c: var TCtx, t: var VmThread, cl: RootRef): YieldReason {.raises: [].} =
  # use local variables to get around the var indirection and allow for better
  # code generation
  var
    stack: seq[StackValue]
    pc = t.pc
    fp = t.frames[^1].start # points to the current local head
    free: seq[uint32]
  swap(t.stack, stack)
  swap(t.free, free)
  defer:
    t.pc = pc
    t.stack = move stack
    t.free = move free

  # performance: pre-allocate the operand stack
  # performance: (maybe) don't use a seq for the operand stack
  # performance: don't use backwards indexing, it's slow (since checks are not
  #              disabled for it)

  template imm8(): int8 = imm8(instr)
  template imm32(): int32 = imm32(instr)
  template imm32_8(): untyped = imm32_8(instr)
  template imm32_16(): untyped = imm32_16(instr)

  template pop(typ: typedesc): untyped =
    # XXX: the builtin pop is too slow :D. A custom seq type needs to be used
    #      instead
    cast[typ](stack.pop())

  template operand(x: static int): untyped =
    stack[stack.len - x]

  template push(val: untyped) =
    stack.add cast[StackValue](val)

  template asgn(idx: static int, val: untyped) =
    let v = val
    stack[stack.len - idx] = cast[StackValue](v)

  template checkmem(address, len): HostPointer =
    let a = address
    var p: HostPointer
    if unlikely(checkmem(c.allocator, cast[VirtualAddr](a), uint(len), p)):
      return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
    p

  template load(typ: typedesc) =
    asgn 1, cast[ptr typ](checkmem(operand(1).intVal + imm32(), sizeof(typ)))[]

  template store(typ: typedesc) =
    let val = pop(typ)
    cast[ptr typ](checkmem(pop(BiggestInt) + imm32(), sizeof(typ)))[] = val

  while true:
    let instr = c.code[pc]

    template binaryOp(op: untyped, name: untyped): untyped =
      let x = pop(name)
      op(cast[name](operand(1)), x)

    template slice(a: VirtualAddr, len): openArray[byte] =
      let x = len
      var p = checkmem(a, x)
      toOpenArray(p, 0, x.int-1)

    case opcode(instr)
    of opcNop: discard
    of opcDrop:
      stack.setLen(stack.len - 1)
    of opcDup:
      # dup
      stack.setLen(stack.len + imm8())
      operand(1) = operand(2)
    of opcSwap:
      swap(operand(1), operand(2))
    of opcLdConst: push c.constants[imm32()].val
    of opcLdImmInt: push imm32()
    of opcLdImmFloat: stack.add cast[StackValue](cast[float32](imm32()).float)
    of opcAddImm: asgn 1, operand(1).uintVal + BiggestUInt imm32()
    of opcAddInt: asgn 1, binaryOp(`+`, BiggestUInt)
    of opcSubInt: asgn 1, binaryOp(`-`, BiggestUInt)
    of opcMulInt: asgn 1, binaryOp(`*`, BiggestUInt)
    # TODO: signed division and modulus need to be safe...
    of opcDivInt: asgn 1, binaryOp(`div`, BiggestInt)
    of opcDivU:   asgn 1, binaryOp(`div`, BiggestUInt)
    of opcModInt: asgn 1, binaryOp(`mod`, BiggestInt)
    of opcModU:   asgn 1, binaryOp(`mod`, BiggestUInt)
    of opcNegInt: asgn 1, -operand(1).intVal
    of opcOffset:
      # use unsigned integers, for overflow-safe arithmetic
      let idx = pop(uint64)
      asgn 1, operand(1).uintVal + (idx * cast[uint64](imm32()))
    of opcBitNot:  asgn 1, not operand(1).uintVal
    of opcNot:
      asgn 1, ord(operand(1).intVal == 0)
    of opcSIntToFloat:
      if imm8() == 8: asgn 1, float64(operand(1).intVal)
      else:           asgn 1, float32(operand(1).intVal)
    of opcUIntToFloat:
      if imm8() == 8: asgn 1, float64(operand(1).uintVal)
      else:           asgn 1, float32(operand(1).uintVal)
    of opcMask:    asgn 1, operand(1).uintVal and ((1'u shl imm8())-1)
    of opcAddFloat:asgn 1, binaryOp(`+`, float)
    of opcSubFloat:asgn 1, binaryOp(`-`, float)
    of opcMulFloat:asgn 1, binaryOp(`*`, float)
    of opcDivFloat:asgn 1, binaryOp(`/`, float)
    of opcNegFloat:asgn 1, -operand(1).floatVal
    of opcBitAnd: asgn 1, binaryOp(`and`, BiggestUInt)
    of opcBitOr:  asgn 1, binaryOp(`or`, BiggestUInt)
    of opcBitXor: asgn 1, binaryOp(`xor`, BiggestUInt)
    of opcShr:    asgn 1, binaryOp(`shr`, BiggestUInt)
    of opcAshr:   asgn 1, binaryOp(`shr`, BiggestInt)
    of opcShl:    asgn 1, binaryOp(`shl`, BiggestUInt)

    # TODO: implement the checked arithmetic operations properly
    of opcAddChck:
      asgn 1, binaryOp(`+`, BiggestInt)
      stack.add StackValue(0)
    of opcSubChck:
      asgn 1, binaryOp(`-`, BiggestInt)
      stack.add StackValue(0)
    of opcMulChck:
      asgn 1, binaryOp(`*`, BiggestInt)
      stack.add StackValue(0)
    of opcDivChck:
      asgn 1, binaryOp(`div`, BiggestInt)
      stack.add StackValue(0)
    of opcModChck:
      asgn 1, binaryOp(`mod`, BiggestInt)
      stack.add StackValue(0)

    of opcSignExtend:
      let imm = uint64(64 - imm8()) # TODO: invert during code generation
      asgn 1, ashr(operand(1).intVal shl imm, imm)
    of opcJmp:
      pc += (imm32() - 1)
    of opcBranch:
      let (rel, inv) = imm32_8()
      if (pop(BiggestInt) xor inv) == 0:
        pc += (rel - 1)
    of opcCall, opcIndCall, opcIndCallCl:
      var (idx, args) = imm32_16()
      var prc: int32
      var bias: int32
      case opcode(instr)
      of opcCall:
        prc = idx
      of opcIndCall:
        prc = operand(1).uintVal.int32
        if unlikely(prc == 0 or prc > c.procs.len):
          return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
        if unlikely(VmTypeId(idx) != c.procs[prc - 1].typ):
          return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessTypeMismatch))
        dec prc
      of opcIndCallCl:
        prc = operand(1).uintVal.int32
        if unlikely(prc == 0 or prc > c.procs.len):
          return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
        if unlikely(VmTypeId(idx) != c.procs[prc - 1].typ):
          return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessTypeMismatch))
        dec prc
        if c.procs[prc].isClosure:
          inc args
          bias = 1
        else:
          bias = 2
        # the proc and env cannot be popped right away, since the procedure might
        # be a stub, in which case the VM yields :(
      else:
        unreachable()

      case c.procs[prc].kind
      of ckDefault:
        # the common case
        # echo "calling: ", c.procs[prc].sym, " at ", c.procs[prc].start
        t.frames.add Frame(start: t.locals.len, comesFrom: pc, ctx: c.allocator.save(), fp: free.len, prc: prc)
        pc = c.procs[prc].start - 1
        fp = t.locals.len
        t.locals.setLen(fp + c.procs[prc].locals.len)
        stack.setLen(stack.len - bias)
      of ckCallback:
        let cb = c.callbacks[c.procs[prc].cbOffset]
        let res = cb(c, toOpenArray(stack, stack.len - args - bias, stack.high - bias), cl)
        # pop the arguments from the stack
        stack.setLen(stack.len - args)
        case res[0]
        of cecNothing: discard
        of cecValue: stack.add res[1]
        else:
          # TODO: raise
          return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
      of ckStub:
        # unlikely case
        return YieldReason(kind: yrkMissingProcedure, entry: FunctionIndex prc)
    of opcEqInt: asgn 1, binaryOp(`==`, BiggestInt)
    of opcLtInt: asgn 1, binaryOp(`<`, BiggestInt)
    of opcLeInt: asgn 1, binaryOp(`<=`, BiggestInt)
    of opcLtu: asgn 1, binaryOp(`<`, BiggestUInt)
    of opcLeu: asgn 1, binaryOp(`<=`, BiggestUInt)
    of opcEqFloat: asgn 1, binaryOp(`==`, float)
    of opcLtFloat: asgn 1, binaryOp(`<`, float)
    of opcLeFloat: asgn 1, binaryOp(`<=`, float)
    of opcLdInt8:   load(uint8)
    of opcLdInt16:  load(uint16)
    of opcLdInt32:  load(uint32)
    of opcLdInt64:  load(uint64)
    of opcLdFlt32:  load(float32)
    of opcLdFlt64:  load(float64)
    of opcWrInt8:   store(uint8)
    of opcWrInt16:  store(uint16)
    of opcWrInt32:  store(uint32)
    of opcWrInt64:  store(uint64)
    of opcWrFlt32:  store(float32)
    of opcWrFlt64:  store(float64)
    of opcWrRef:
      let val = pop(ForeignRef)
      let dst = cast[ptr ForeignRef](checkmem(pop(BiggestInt) + imm32(), 8))
      if val.uint64 != 0:
        c.allocator.incRef(val)
      if dst[].uint64 != 0:
        c.allocator.decRef(dst[])
      dst[] = val
    of opcStackAlloc:
      let typ = addr c.types[VmTypeId imm32()]
      let (p, cell) = c.allocator.allocStack(typ.size, (1'u shl typ.align), VmTypeId(imm32()))
      if unlikely(p == 0):
        # TODO: report a stack overflow error
        return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
      zeroMem(c.allocator.translate(p), typ.size)
      if vtfDataOnly notin typ.flags:
        free.add cell
      stack.add cast[StackValue](p)
    of opcCopy:
      # RTTI-based copy
      let typ = imm32()
      let b = pop(VirtualAddr)
      let a = pop(VirtualAddr)
      if unlikely(checkedCopy(a, b, c.types, VmTypeId typ, c.allocator)):
        return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))

      if unlikely(c.allocator.zct.len > 1024):
        gc(c, stack, t)
      # if unlikely(cleanup(c.allocator, c.types)):
      #   return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
    of opcDestroy:
      # RTTI-based destroy
      let typ = imm32()
      let a = pop(VirtualAddr)
      if unlikely(checkedDestroy(a, c.types, VmTypeId typ, c.allocator)):
        return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
    of opcReset:
      let typ = VmTypeId imm32()
      let a = pop(VirtualAddr)
      if unlikely(checkedDestroy(a, c.types, typ, c.allocator)):
        return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
      zeroMem(c.allocator.translate(a), c.types[typ].size)
    of opcMemCopy:
      let len = pop(BiggestUInt)
      let src = pop(VirtualAddr)
      let dst = pop(VirtualAddr)
      copyMem(checkmem(dst, len), checkmem(src, len), len)
    of opcMemClear:
      let len = pop(BiggestUInt)
      let dst = pop(BiggestUInt)
      zeroMem(checkmem(dst, len), len)
    of opcGetGlobal:
      let (pri, sec) = imm32_8()
      stack.add c.globals[sec][pri].val
    of opcGetLocal:
      stack.add t.locals[fp + imm32()]
    of opcSetLocal:
      t.locals[fp + imm32()] = operand(1)
    of opcPopLocal:
      t.locals[fp + imm32()] = stack.pop()
    of opcEnter:
      let next = pc + imm32()
      t.locals[fp + imm32(c.code[next])] = StackValue(pc + 1)
      pc = next
    of opcFinally:
      unreachable("never executed")
    of opcFinallyEnd:
      let (isError, target) = decodeControl(t.locals[fp + imm32()].uintVal)
      if isError: # continue the EH thread
        # TODO: Result cannot be used here, since the operations on it can
        #       raises exceptions. Quite sad, but oh well
        {.cast(raises: []).}:
          let r = resumeEh(c, t, t.frames.high)
          fp = t.frames[^1].start
          if likely(r.isOk):
            pc = r.take()
            if c.code[pc].opcode == opcFinally:
              t.locals[fp + imm32(c.code[pc])] = StackValue(fromEhBit)
          else:
            let err = r.takeErr()
            return YieldReason(kind: yrkUnhandledException, exc: err.addrVal)
      else: # jump to the saved position
        pc = PrgCtr(target)
      dec pc
    of opcLeave:
      let (rel, mode) = imm32_8()
      if mode == 0:
        echo "missing: exception handling (leave)"
      else:
        let (fromEh, _) = decodeControl(t.locals[fp + imm32(c.code[pc + rel])].uintVal)
        if fromEh:
          t.ehStack.setLen(t.ehStack.len - 1)
      # TODO: current exception handling is missing
    of opcRet:
      let top = t.frames.pop()
      t.locals.setLen(top.start)
      for i in top.fp..<free.len:
        let (typ, p) = c.allocator.stack(free[i])
        if unlikely(destroy(p, c.types, typ, c.allocator)):
          # echo "error for: ", c.types[typ], " at ", c.allocator.mapBack(p).int
          return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
      free.setLen(top.fp)

      c.allocator.restore(top.ctx)

      if likely(t.frames.len > 0):
        # the common case
        pc = top.comesFrom
        fp = t.frames[^1].start

        # if t.frames[^1].sp + ord(c.types[c.types.returnType(c.procs[t.frames[^1].prc].typ)].kind != akVoid) != stack.len:
        #   echo "expect: ", t.frames[^1].sp
        #   echo "got: ", stack.len
        #   echo "bias: ", ord(c.types[c.types.returnType(c.procs[t.frames[^1].prc].typ)].kind != akVoid)
        #   return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtErrInternal))
      else:
        let ret = c.types.returnType(c.procs[top.prc.int].typ)
        if c.types[ret].kind == akVoid:
          return YieldReason(kind: yrkDone)
        else:
          return YieldReason(kind: yrkDone, reg: some stack.pop(), typ: ret)

    of opcLeSet:
      let size = imm32()
      let other = pop(VirtualAddr)
      asgn 1, ord(bitSetContains(slice(operand(1).addrVal, size), slice(other, size)))
    of opcEqSet:
      let size = imm32()
      let other = pop(VirtualAddr)
      asgn 1, ord(bitSetEquals(slice(operand(1).addrVal, size), slice(other, size)))
    of opcLtSet:
      let size = imm32()
      let other = pop(VirtualAddr)
      asgn 1, ord(bitSetContains(slice(operand(1).addrVal, size), slice(other, size)) and
                  not bitSetEquals(slice(operand(1).addrVal, size), slice(other, size)))
    of opcMulSet:
      let size = imm32()
      let b = checkmem(pop(VirtualAddr), size)
      let a = checkmem(pop(VirtualAddr), size)
      var dst = checkmem(pop(VirtualAddr), size)
      copyMem(dst, a, size)
      bitSetIntersect(toOpenArray(dst, 0, size.int-1), toOpenArray(b, 0, size.int-1))
    of opcPlusSet:
      let size = imm32()
      let b = checkmem(pop(VirtualAddr), size)
      let a = checkmem(pop(VirtualAddr), size)
      var dst = checkmem(pop(VirtualAddr), size)
      copyMem(dst, a, size)
      bitSetUnion(toOpenArray(dst, 0, size.int-1), toOpenArray(b, 0, size.int-1))
    of opcMinusSet:
      let size = imm32()
      let b = checkmem(pop(VirtualAddr), size)
      let a = checkmem(pop(VirtualAddr), size)
      var dst = checkmem(pop(VirtualAddr), size)
      copyMem(dst, a, size)
      bitSetDiff(toOpenArray(dst, 0, size.int-1), toOpenArray(b, 0, size.int-1))
    of opcIncl:
      let size = imm32()
      let val = pop(BiggestInt)
      if val notin 0 .. int(size * 8):
        return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
      let a = pop(VirtualAddr)
      bitSetIncl(slice(a, size), val)
    of opcInclRange:
      let size = imm32()
      let b = pop(BiggestInt)
      let a = pop(BiggestInt)
      if a notin 0 .. int(size * 8) or (b notin 0..int(size * 8)):
        return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
      let s = pop(VirtualAddr)
      bitSetInclRange(slice(s, size), a .. b)
    of opcExcl:
      let size = imm32()
      let val = pop(BiggestInt)
      if unlikely(val notin 0 .. int(size * 8)):
        return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
      let a = pop(VirtualAddr)
      bitSetExcl(slice(a, size), val)
    of opcInSet:
      let size = imm32()
      let val = pop(BiggestInt)
      if unlikely(val notin 0 .. int(size * 8)):
        return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
      asgn 1, ord bitSetIn(slice(operand(1).addrVal, size), val)
    of opcTrim:
      # TODO: undo the last N stack allocations
      echo "missing: trim"
    of opcCheck:
      let typ = VmTypeId imm32()
      let res = mapInteriorPointerToCell(c.allocator, operand(1).addrVal)
      if unlikely(res.p.isNil):
        return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessOutOfBounds))
      # untyped memory isn't type checked
      if res.typ != VoidType and unlikely(typecheck(c.types, res.typ, res.p, res.offset, typ)):
        # TODO: currently disabled due to seqs sometimes being treated as
        #       their underlying record type. The typechecker needs to support
        #       this case
        discard
        # return YieldReason(kind: yrkError, error: VmEvent(kind: vmEvtAccessTypeMismatch))

    of opcRaise:
      let reraise = imm8()
      if reraise == 0:
        echo "start: ", operand(1)
        {.cast(raises: []).}:
          let r = opRaise(c, t, pc, stack.pop())
          if unlikely(r.isErr):
            let err = r.takeErr()
            echo "unhandled: ", err
            # XXX: no stacktrace at the moment. It should ideally just be part
            #      of the RT exception object
            return YieldReason(kind: yrkUnhandledException, exc: err.addrVal)
          pc = r.take()
      else:
        echo "missing: re-raise"
    of opcYield:
      inc pc
      let (num, reason) = imm32_8(instr)
      return YieldReason(kind: yrkUser, reason: reason, args: num)
    of opcReinterpI64, opcReinterpF64:
      discard "a no-op"
    of opcReinterpF32:
      asgn 1, cast[float32](cast[uint32](operand(1).uintVal))
    of opcReinterpI32:
      asgn 1, cast[uint32]((operand(1).floatVal).float32)
    of opcFloatToSInt:
      # TODO: the conversions need to never raise overflow errors
      let arg = operand(1).floatVal
      case imm8()
      of 8: asgn 1, int64(arg)
      of 4: asgn 1, int64(arg)
      of 2: asgn 1, int32(arg)
      of 1: asgn 1, int8(arg)
      else: unreachable()
    of opcFloatToUint:
      # XXX: hm, this looks like nonsense?
      let width = imm8()
      var val = cast[uint64](int64(operand(1).floatVal))
      if width < 8:
        val = val and ((1'u64 shl (width * 8)) - 1)

    inc pc

proc `=copy`*(x: var VmThread, y: VmThread) {.error.}

proc initVmThread*(c: var TCtx, prc: FunctionIndex, params: sink seq[StackValue]): VmThread =
  VmThread(pc: c.procs[prc.int].start,
           stack: params,
           locals: newSeq[StackValue](c.procs[prc.int].locals.len),
           #loopIterations: c.config.maxLoopIterationsVM,
           frames: @[Frame(prc: prc.int)])

proc dispose*(c: var TCtx, t: sink VmThread) =
  ## Cleans up and frees all VM data owned by `t`.
  # TODO: implement

template source*(c: TCtx, t: VmThread): TLineInfo =
  ## Gets the source-code information for the instruction the program counter
  ## of `t` currently points to
  c.debug[t.pc]

template `[]`*(t: VmThread, i: Natural): TStackFrame =
  ## Returns `t`'s stack frame at index `i`.
  t.sframes[i]

proc pop*(x: var VmThread): StackValue =
  x.stack.pop()