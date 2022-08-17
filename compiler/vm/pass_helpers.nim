
import compiler/vm/vmir

template genIfNot*(cr: var IrCursor, cond: IRIndex, code: untyped) =
  let condVal = cond

  let j = cr.newJoinPoint()
  cr.insertBranch(condVal, j)
  code
  cr.insertGoto(j)
  cr.insertJoin(j)

func genTempOf*(cr: var IrCursor, src: IRIndex, typ: TypeId): int =
  result = cr.newLocal(lkTemp, typ)
  cr.insertAsgn(askInit, cr.insertLocalRef(result), src) # XXX: should be both init and shallow

template argAt*(ir: IrStore3, cr: IrCursor, i: Natural): IRIndex =
  ## Temporary helper until ``IRIndex`` is used in more places
  {.line.}:
    ir.args(cr.position, i)