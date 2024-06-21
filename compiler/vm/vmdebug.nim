
import std/[tables, strutils]
import compiler/ast/[ast_types, ast]
import compiler/vm/[vmdef, newvm, vmalloc, vmtypes, vmutils, vmobjects, vmchecks]
import compiler/front/options
import compiler/utils/[idioms]

import std/options as std_options

type
  BreakpointKind* = enum
    bpNone
    bpReturn
    bpCall
    bpYield
    bpStep

  VmDebugger* = object
    breakOn*: BreakpointKind
    name: string
    map: Table[PrgCtr, TInstr]

proc dump(c: TCtx, t: VmThread) =
  for it in t.frames[^1].start..t.locals.high:
    echo "local[", it-t.frames[^1].start, "] = ", t.locals[it], " | ", c.procs[t.frames[^1].prc.int].locals[it - t.frames[^1].start]

proc frame(c: TCtx, t:VmThread, frame: Frame) =
  for it in frame.start..t.locals.high:
    echo "local[", it-frame.start, "] = ", t.locals[it], " | ", c.procs[frame.prc.int].locals[it - frame.start]

proc trace(t: var VmThread, c: TCtx) =
  for i, it in t.frames.pairs:
    echo repeat("  ", i), i, ": ", c.procs[it.prc].sym#, " line: ", c.procs[it.prc].sym.info.line

proc restore(d: var VmDebugger, c: var VmEnv) =
  for pos, instr in d.map.pairs:
    c.code[pos] = instr
  d.map.clear()

proc debugInstr(): TInstr =
  TInstr(opcYield.TInstrType or (2.TInstrType shl regBShift))

proc patch(i: var TInstr, d: var VmDebugger, pc: PrgCtr) =
  d.map[pc] = i
  i = debugInstr()

proc patch(c: var VmEnv, d: var VmDebugger, pc: PrgCtr) =
  patch(c.code[pc], d, pc)

proc patchProcs(d: var VmDebugger, c: var VmEnv) =
  for p in c.procs.items:
    if p.sym != nil and p.sym.name.s == d.name and p.kind == ckDefault:
      patch(c, d, p.start + 1)

proc update*(d: var VmDebugger, c: var VmEnv, pc: PrgCtr) =
  restore(d, c)
  case d.breakOn
  of bpCall:
    patchProcs(d, c)
  of bpYield:
    for p, it in c.code.mpairs:
      if it.opcode == opcYield:
        patch(it, d, p)
  of bpStep:
    # XXX: step support is underdeveloped
    case c.code[pc].opcode
    of opcBranch:
      patch(c, d, pc + 1)
      patch(c, d, c.code[pc].imm32 + pc)
    of opcJmp:
      patch(c, d, c.code[pc].imm32 + pc)
    else:
      patch(c, d, pc + 1)
  of bpReturn:
    # TODO: only break on returns within the current procedure
    for p, it in c.code.mpairs:
      if it.opcode == opcRet:
        patch(it, d, p)
  of bpNone:
    discard

proc debug*(debug: var VmDebugger, t: var VmThread, c: var VmEnv, config: ConfigRef) =
  restore(debug, c)
  var str = readLine(stdin)
  while str.len > 0:
    if str == "dump":
      dump(c, t)
    elif str.startsWith "frame":
      let f = parseInt str.split(' ')[1]
      frame(c, t, t.frames[^f])
    elif str == "stack":
      for i, it in t.stack.pairs:
        echo i, ": ", it
    elif str == "trace":
      trace(t, c)
    elif str == "dis":
      echo renderCodeListing(config, nil, codeListing(c, max(t.pc - 5, 0), t.pc + 5))
    elif str == "continue":
      debug.breakOn = bpNone
      update(debug, c, t.pc)
      return
    elif str.startsWith "next":
      debug.name = str.split(' ')[1]
      debug.breakOn = bpCall
      update(debug, c, t.pc)
      return
    elif str == "yield":
      debug.breakOn = bpYield
      update(debug, c, t.pc)
      return
    elif str == "ret":
      debug.breakOn = bpReturn
      update(debug, c, t.pc)
      return
    elif str == "alloc":
      show(c.allocator)
    elif str.startsWith("read"):
      let args = str.split(' ')
      let ad = parseInt args[1]
      let x = mapInteriorPointerToCell(c.allocator, VirtualAddr(ad))
      if x.p == nil:
        echo "not allocated?"
      else:
        echo "start: ", x.base.int
        echo "size: ", x.size
        echo "typ: ", c.types[x.typ]
        echo "value: ", x.p.load(StackValue)
    elif str.startsWith("typeof"):
      let args = str.split(' ')
      let ad = parseInt args[1]
      let x = mapInteriorPointerToCell(c.allocator, VirtualAddr(ad))
      if x.p == nil:
        echo "not allocated?"
      else:
        var closest = 0'u
        let typ = c.types.getType(x.typ, x.p, x.offset, closest)
        if typ.isSome:
          echo "typ: ", c.types[typ.unsafeGet], " offset: ", closest, " id: ", typ.unsafeGet
        else:
          echo "has no type"
    elif str.startsWith("proc"):
      let args = str.split(' ')
      let p = c.procs[parseInt args[1]]
      echo "name: ", (if p.sym != nil: p.sym.name.s else: "<nil>"), " typ: ", c.types[p.typ], " kind: ", p.kind, " closure?: ", p.isClosure

    str = readLine(stdin)

  debug.breakOn = bpStep
  update(debug, c, t.pc)

  debugEcho "next: ", t.pc, " -- ", c.code[t.pc].opcode, " a: ", imm32(c.code[t.pc]), " c: ", imm8(c.code[t.pc])
