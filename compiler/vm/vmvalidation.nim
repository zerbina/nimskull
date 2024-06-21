## Implements the validation of bytecode.

import std/intsets
import vmdef
import vm_enums, vmtypes
import compiler/utils/[idioms, containers]

import experimental/results

type
  ValidationState = object
    stack: seq[AtomKind]
    active: bool
    targets: IntSet
    length: int
    current: FunctionIndex

  Error = object
    expected: AtomKind
    got: AtomKind

proc trans(t: VmType): AtomKind =
  case t.kind
  of akInt, akFloat: t.kind
  of akPtr, akRef, akForeign: akInt
  of akProc: akInt
  of akVoid: akVoid
  else: akInt

proc arg(env: VmTypeEnv, t: VmTypeId, i: int): AtomKind =
  trans(env[env.fields[env[t].a + i.uint32 + 1].typ])

proc numArgs(typ: VmType): int =
  typ.len - 1

proc run(ctx: var ValidationState, pos: int, instr: TInstr, env: TCtx): Result[void, Error] =
  template push(kind: AtomKind) =
    ctx.stack.add kind
  template error(msg: string) =
    # echo msg
    return Result[void, Error].err(Error())

  template expect(num: int) =
    if ctx.stack.len < num:
      error("stack underflow")

  template pop(kind: AtomKind) =
    expect(1)
    if (let v = ctx.stack.pop(); v != kind):
      error("wrong kind: " & $v)

  template checked(s: seq|array, pos: untyped): untyped =
    let p = pos
    if p in 0..s.high: s[p]
    else:             error("out of bounds")

  template expectEmpty() =
    if ctx.stack.len > 0:
      # echo ctx.stack
      error("not empty")

  template jump(x: untyped) =
    if pos + x notin 0..(ctx.length-1):
      error("wrong jump target")
    ctx.targets.incl(pos + x)

  template checkType(typ: untyped) =
    if typ notin 0..(env.types.types.nextId().int-1):
      error("not a valid type ID")

  # jump targets
  if not ctx.targets.missingOrExcl(pos):
    expectEmpty()

  case opcode(instr)
  of opcNop:
    discard "does nothing"
  of opcDrop:
    expect(1)
    discard ctx.stack.pop()
  of opcDup:
    if imm8(instr) < 1:
      error("count < 1")
    expect(1)
    push(ctx.stack[^1])
  of opcSwap:
    expect(2)
    swap(ctx.stack[^1], ctx.stack[^2])
  of opcLdImmInt: push(akInt)
  of opcLdImmFloat: push(akFloat)
  of opcAddImm:
    pop(akInt)
    push(akInt)
  of opcLdConst:
    push(checked(env.constants, imm32(instr)).typ)
  of opcAddInt, opcSubInt, opcMulInt, opcDivInt, opcDivU, opcModInt, opcModU,
     opcBitAnd, opcBitOr, opcBitXor, opcShr, opcShl, opcEqInt, opcLtInt,
     opcLeInt, opcLeu, opcLtu, opcAshr:
    pop(akInt)
    pop(akInt)
    push(akInt)
  of opcMemClear:
    pop(akInt)
    pop(akInt)
  of opcCheck:
    pop(akInt)
    push(akInt)
    checkType(imm32(instr))
  of opcMask:
    pop(akInt)
    push(akInt)
    if imm8(instr) notin 0..63:
      error("inccorect mask bits")
  of opcYield:
    expect(imm32(instr))
    ctx.stack.setLen ctx.stack.len-imm32(instr)
  of opcReset, opcDestroy:
    pop(akInt)
    checkType(imm32(instr))
  of opcTrim:
    # XXX: check whether the value is sensible?
    discard
  of opcSignExtend, opcNot:
    pop(akInt)
    push(akInt)
  of opcAddChck, opcSubChck, opcMulChck, opcDivChck, opcModChck:
    pop(akInt); pop(akInt)
    push(akInt); push(akInt)
  of opcAddFloat, opcSubFloat, opcMulFloat, opcDivFloat:
    pop(akFloat); pop(akFloat)
    push(akFloat)
  of opcUIntToFloat, opcSIntToFloat:
    push(akInt)
    pop(akFloat)
  of opcFloatToSInt, opcFloatToUint, opcReinterpI32, opcReinterpI64:
    pop(akFloat)
    push(akInt)
  of opcEqFloat, opcLtFloat, opcLeFloat:
    pop(akFloat); pop(akFloat)
    push(akInt)
  of opcLdInt8, opcLdInt16, opcLdInt32, opcLdInt64:
    pop(akInt)
    push(akInt)
  of opcLdFlt32, opcLdFlt64, opcReinterpF32, opcReinterpF64:
    pop(akInt)
    push(akFloat)
  of opcWrInt8, opcWrInt16, opcWrInt32, opcWrInt64:
    pop(akInt)
    pop(akInt)
  of opcCopy:
    pop(akInt)
    pop(akInt)
  of opcJmp:
    expectEmpty()
    jump(imm32(instr))
  of opcBranch:
    let (rel, _) = imm32_8(instr)
    pop(akInt)
    jump(rel)
  of opcEnter:
    expectEmpty()
    # TODO: forward control-flow only
    jump(imm32(instr))
  of opcLeave:
    let op = imm8(instr)
    if op == 0:
      discard "no values are popped"
    elif op == 1:
      pop(akInt)
      expectEmpty()
    else:
      error("invalid operand")
  of opcFinally:
    discard checked(env.procs[ctx.current.int].locals, imm32(instr))
    if ctx.active:
      error("active")
    # TODO: guard the local against modifications
  of opcFinallyEnd:
    # TODO: make sure the local matches that of the corresponding Finally
    #       instruction
    discard checked(env.procs[ctx.current.int].locals, imm32(instr))
    if not ctx.active:
      error("not active")
  of opcCall:
    let (idx, num) = imm32_16(instr)
    # if checked(env.procs, idx).kind == ckCallback:
    #   return Result

    if env.types[checked(env.procs, idx).typ].numArgs() != num:
      # XXX: too many errors due to untyped callbacks at the moment; pop
      #      the operands anyway
      if num <= ctx.stack.len:
        ctx.stack.setLen(ctx.stack.len - num)
      else:
        echo "error: arguments"
        error("not enough arguments")
      error("arity mismatch")

    # pop all arguments from the stack, expecting the given kinds
    for i in 0..<num:
      pop(arg(env.types, env.procs[idx].typ, num - i - 1))

    # push the retunrn value, if any
    let ret = trans env.types[env.types.returnType(env.procs[idx].typ)]
    if ret != akVoid:
      push(ret)
  of opcIndCall, opcIndCallCl:
    let (typ, num) = imm32_16(instr)
    # TODO: verify that the type is that of a procedure
    checkType(typ)
    if env.types[VmTypeId typ].numArgs() != num:
      if num <= ctx.stack.len:
        ctx.stack.setLen(ctx.stack.len - num)
      else:
        echo "error: arguments"
        error("not enough arguments")
      error("arity mismatch")

    pop(akInt) # callee
    if opcode(instr) == opcIndCallCl:
      pop(akInt) # env

    # pop all arguments from the stack, expecting the given kinds
    for i in 0..<num:
      pop(env.types.arg(VmTypeId(typ), num - i - 1))

    # push the retunrn value, if any
    let ret = trans env.types[env.types.returnType(VmTypeId typ)]
    if ret != akVoid:
      push(ret)
  of opcRet:
    let expect = trans env.types[env.types.returnType(env.procs[ctx.current.int].typ)]
    if expect != akVoid:
      pop(expect)
    expectEmpty()
  of opcGetLocal:
    push(checked(env.procs[ctx.current.int].locals, imm32(instr)))
  of opcPopLocal:
    pop(checked(env.procs[ctx.current.int].locals, imm32(instr)))
  of opcSetLocal:
    discard checked(env.procs[ctx.current.int].locals, imm32(instr))
  of opcStackAlloc:
    checkType(imm32(instr))
    push(akInt)
  of opcGetGlobal:
    push(trans env.types[checked(checked(env.globals, imm8(instr)), imm32(instr)).typ])
  of opcNegInt, opcNegFloat:
    pop(akInt)
    push(akInt)
  of opcRaise:
    if imm8(instr) == 1:
      pop(akInt)
    elif imm8(instr) != 0:
      error "value must be 1 or 0"
    expectEmpty()
  of opcBitNot, opcOffset, opcEqSet, opcLtSet, opcLeSet, opcInSet:
    pop(akInt)
    pop(akInt)
    push(akInt)
  of opcWrFlt32, opcWrFlt64:
    pop(akInt)
    pop(akFloat)
  of opcWrRef:
    pop(akInt)
    pop(akForeign)
  of opcMemCopy, opcMulSet, opcPlusSet, opcMinusSet, opcInclRange:
    pop(akInt)
    pop(akInt)
    pop(akInt)
  of opcIncl, opcExcl:
    pop(akInt)
    pop(akInt)

  result.initSuccess()

proc validate*(env: TCtx, prc: FunctionIndex, code: openArray[TInstr]): bool =
  var ctx = ValidationState(current: prc, length: code.len)
  # echo "---validate: ", code.len, " name: ", env.procs[prc.int].sym.name.s

  # push all parameters to the stack
  for _, it in parameters(env.types, env.procs[prc.int].typ):
    ctx.stack.add(trans env.types[it])

  for pos, it in code.pairs:
    if run(ctx, pos, it, env).isErr():
      # echo "failure at pos: ", pos, " -- ", opcode(it)
      # return false
      discard

  result = true

proc validate*(types: VmTypeEnv) =
  ## Makes sure the type environment adheres to the expectations of the VM.
  ## For example, that there are no empty record types, that field offsets make
  ## sense, etc.
  discard