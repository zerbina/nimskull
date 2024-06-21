## This module contains some utility procedures for inspecting VM-related
## data.
##
## The VM doesn't depend on the procedures here in order to
## function - they are only meant as a logging and debugging aid.

import
  std/[
    intsets,
    strutils
  ],
  compiler/ast/[
    ast,
    lineinfos,
    renderer,
    typesrenderer,
  ],
  compiler/front/[
    options
  ],
  compiler/vm/[
    vmdef
  ]

from compiler/front/msgs import toFileLineCol

type
  DebugVmCodeEntry* = object
    isTarget*: bool
    info*: TLineInfo
    pc*: int
    idx*: int
    opc*: Opcode
    a*: int32
    b*: int16
    c*: int8
    name: string


proc codeListing*(c: TCtx; start = 0; last = -1): seq[DebugVmCodeEntry] =
  ## Produces a listing of the instructions in `c` that are located in the
  ## instruction range ``start..last``. If ``last < 0``, then all instructions
  ## after position `start` are included in the listing. The instructions are
  ## ordered by their position
  let last =
    if last < 0: c.code.high
    else:        min(last, c.code.high)

  # first iteration: compute all necessary labels:
  var jumpTargets = initIntSet()
  for i in start..last:
    let x = c.code[i]
    if x.opcode in {opcJmp, opcBranch, opcLeave, opcEnter}:
      jumpTargets.incl(i+x.imm32())

  # because some instructions take up more than one instruction word, there's
  # not a 1-to-1 mapping between instruction words and the resulting list
  # entries
  result = newSeqOfCap[DebugVmCodeEntry](last - start + 1)

  var i = start
  while i <= last:
    let
      x = c.code[i]
      opc = opcode(x)

    var code = DebugVmCodeEntry(
      pc: i - start,
      opc: opc,
      a: x.imm32,
      b: x.imm32_16[1],
      c: x.imm8,
      idx: (x.imm32 + i) - start,
      info: c.debug[i],
      isTarget: i in jumpTargets
    )
    if opc == opcCall and c.procs[code.a].sym != nil:
      code.name = c.procs[code.a].sym.name.s
    result.add code
    inc i

proc renderCodeListing*(config: ConfigRef, sym: PSym,
                        entries: seq[DebugVmCodeEntry]): string =
  ## Renders the code listing `entries` to text. `sym` is an optional symbol
  ## that, if provided, is used for providing additional context.
  if sym != nil:
    result = "Code Listing for '$1' $2" %
             [sym.name.s, config.toFileLineCol(sym.info)]
  else:
    result = "Code Listing for <unknown>"

  result.add "\n\n"

  var line: string # re-used for efficiency
  for e in entries:
    if e.isTarget:
      result.addf("L:$1\n", e.pc)

    func `$<`[T](arg: T): string =
      alignLeft($arg, 5)
    func `$<`(opc: TOpcode): string =
      # cut off the enum prefix
      alignLeft(substr($opc, 3), 12)

    line.setLen(0)

    case e.opc
    of opcIndCall, opcIndCallCl:
      line.addf("  $# $# $#", $<e.opc, $<e.a, $<e.b)
    of opcCall:
      line.addf("  $# $# $# # $#", $<e.opc, $<e.a, $<e.b, e.name)
    of opcJmp, opcEnter:
      line.addf("  $# L$#", $<e.opc, $<e.idx)
    of opcBranch:
      line.addf("  $# L$# invert:$#", $<e.opc, $<e.idx, $<e.c)
    of opcFinally, opcFinallyEnd, opcLdImmInt, opcGetLocal, opcGetGlobal, opcWrInt8..opcWrFlt64, opcCopy, opcStackAlloc, opcSetLocal, opcPopLocal, opcAddImm, opcLdInt8..opcLdFlt64, opcOffset, opcCheck, opcDestroy, opcReset:
      line.addf("  $# $#", $<e.opc, $<e.a)
    of opcSignExtend:
      line.addf("  $# $#", $<e.opc, $<e.c)
    of opcYield:
      line.addf("  $# $# reason:$#", $<e.opc, $<e.a, $<e.c)
    else:
      line.addf("  $#", $<e.opc)

    result.add alignLeft(line, 48)
    result.add toFileLineCol(config, e.info)
    result.add "\n"

  # one final line break
  result.add "\n"