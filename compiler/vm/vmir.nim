import compiler/ast/ast_types
import std/tables

import compiler/vm/irtypes

from compiler/vm/vmdef import unreachable

export irtypes

const useNodeTraces {.booldefine.} = false

type IRIndex* = int
const InvalidIndex* = -1 # XXX: it would be better for `InvalidIndex` to be '0'

type
  PathIndex = #[distinct]# IRIndex
    ## The ID of a path expression. Currently an `IRIndex`, but paths might be
    ## stored in a separate list later on

  JoinPoint* = #[distinct]# IRIndex

  IrNodeKind3* = enum
    ntkAsgn
    ntkUse
    ntkConsume
    ntkCall
    ntkAddr
    ntkDeref
    ntkLocEnd

    ntkProc # reference to a procedure
    ntkParam # reference to a parameter
    ntkSym
    ntkRoot # a handle
    ntkLocal # references a local
    ntkLit
    ntkImm

    ntkPathArr
    ntkPathObj
    ntkConv
    ntkCast

    ntkBranch
    ntkGoto
    ntkJoin
    ntkGotoLink
    ntkGotoCont # goto with continuation
    ntkContinue # goto the active continuation

    # phase 4
    ntkLoad
    ntkWrite

  AssignKind* = enum
    askShallow
    askInit # XXX: an assign can be both an init assign and a shallow assign
    askMove
    askCopy

    askDiscr # XXX: would be simpler if this would be a magic call instead (e.g. `switch`)

  BuiltinCall* = enum
    ## Very similar to ``TMagic`` with the difference that a `BuiltinCall` is
    ## only used by the back-end. This is meant as a way to leave ``TMagic``
    ## unmodified
    bcError # encodes an error in the IR # XXX: make this a dedicated node?
    bcNewClosure # setup closure
    bcSwitch # switch variant branch
    bcMatch # 'of' branch
    bcGetBranchIndex # compute the branch index
    bcRaise
    bcTestError
    bcRaiseFieldErr
    bcInclRange
    bcRangeCheck
    bcOverflowCheck

    bcNew

    bcAccessEnv ## access the current procedure's closure environment

    bcUnlikely # XXX: alternatively, turn `system.unlikelyProc` into a .compilerproc

  CallKind* = enum
    ckNormal
    ckBuiltin
    ckMagic

  IrNode3* = object
    case kind: IrNodeKind3
    of ntkAsgn:
      asgnKind: AssignKind
      wrDst, wrSrc: IRIndex
      discard
    of ntkImm:
      immediate: uint32
    of ntkSym:
      sym: SymId
    of ntkPathObj:
      field: int16
      objSrc: PathIndex
    of ntkPathArr:
      arrSrc: PathIndex
      idx: IRIndex
    of ntkLit:
      litIdx: int
    of ntkLocal:
      local: int
    of ntkProc:
      procId: ProcId
    of ntkParam:
      param: int
    of ntkAddr, ntkDeref:
      addrLoc: PathIndex
    of ntkGoto, ntkGotoLink:
      gotoTarget: JoinPoint
    of ntkBranch:
      cond: IRIndex
      target: JoinPoint
    of ntkGotoCont:
      contTarget: JoinPoint
      contThen: JoinPoint
    of ntkCall:
      case ckind: CallKind
      of ckNormal: callee: IRIndex
      of ckBuiltin:
        builtin: BuiltinCall
      of ckMagic:
        # used for compiler inserted magic calls
        magic: TMagic

      # XXX: only relevant for ckMagic and ckBuiltin
      typ: TypeId ## the return type. Only valid for ``ckMagic``
                  ## and ``ckBuiltin``

      numArgs: uint32
    of ntkUse, ntkConsume:
      theLoc: IRIndex
    of ntkConv, ntkCast:
      srcOp: IRIndex
      destTyp: TypeId

    of ntkJoin:
      joinPoint: JoinPoint
    else:
      discard

  Literal* = tuple[val: PNode, typ: TypeId]

  LocalKind* = enum
    lkTemp
    lkVar
    lkLet

  Local* = object
    ## Holds information about a procedure-local ``var|let``
    kind*: LocalKind
    typ*: TypeId
    decl*: DeclId ## information for the code-generator
    loc*: LocDesc ## additional information describing the location

  IrStore3* = object
    nodes: seq[IrNode3]
    #syms: seq[PSym]
    numJoins: int
    literals: seq[Literal]
    locals: seq[Local]

    localSrc: seq[seq[StackTraceEntry]]
    sources: seq[seq[StackTraceEntry]] # the stack trace of where each node was added

    # XXX: to temporarily make things easier, the owning procedure's ID is stored here (will be moved elsewhere later)
    owner*: ProcId

  IrEnv* = object
    ##
    syms*: SymbolEnv
    types*: TypeEnv
    procs*: ProcedureEnv

  IrNodeHdr = object
    ## The format of a node header. The type is just meant as visualization.
    kind {.bitsize: 8.}: int
    len {.bitsize: 24.}: int

  IrNode4* = distinct uint32
    ## The not-yet-used next iteration of `IrNode`. ``IrNode3`` is quite large
    ## (currently 32-byte, moving to ``uint32`` for ``IRIndex`` would reduce
    ## it to 24), but not all node kinds require the same amount of storage.
    ## So instead, a variable-length encoding is used. Each node starts
    ## with a header (see ``IrNodeHdr``) followed by ``len`` 32-bit fields.
    ##
    ## The nodes indices are no longer monotonically increasing, but that's
    ## not a problem. Iteration will become a bit slower, since the index
    ## can't be incremented by static value and has a data-dependency on the
    ## current node.
    ##
    ## Accessing the content of nodes will use one of the following
    ## approaches (or a mix of them):
    ##
    ## .. code::nim
    ##
    ##    # approach 1
    ##    func typ(nodes: IrNodes, n: IRIndex): TypeId
    ##      ## Only allowed for ``ntkCall|ntkConv|ntkCast`` nodes
    ##
    ##    # approach 2
    ##    type CallNode = object
    ##      ...
    ##
    ##    func call(nodes: IrNodes, n: IRIndex): CallNode
    ##      ## Casts the data at `n` into a ``CallNode``. It's illegal to use
    ##      ## this procedure if the node a `n` is not an ``ntkCall`` node

  IrNodes = object
    data: seq[IrNode4]


func traceFor*(s: IrStore3, i: IRIndex): seq[StackTraceEntry] =
  when useNodeTraces:
    s.sources[i]

func traceForLocal*(s: IrStore3, i: int): seq[StackTraceEntry] =
  when useNodeTraces:
    s.localSrc[i]


func add(x: var IrStore3, n: sink IrNode3): IRIndex =
  result = x.nodes.len.IRIndex
  x.nodes.add n
  when useNodeTraces:
    {.noSideEffect.}:
      x.sources.add getStackTraceEntries()

## version 2/3


func addLocal*(c: var IrStore3, data: Local): int =
  assert data.typ != NoneType
  c.locals.add data
  result = c.locals.high
  when useNodeTraces:
    {.noSideEffect.}:
      c.localSrc.add(getStackTraceEntries())


func irContinue*(c: var IrStore3) =
  discard c.add(IrNode3(kind: ntkContinue))

func irUse*(c: var IrStore3, loc: IRIndex): IRIndex =
  c.add(IrNode3(kind: ntkUse, theLoc: loc))

proc irSym*(c: var IrStore3, sym: SymId): IRIndex =
  # TODO: don't add duplicate items?
  assert sym != NoneSymbol
  #c.syms.add(sym)
  c.add(IrNode3(kind: ntkSym, sym: sym))

func irDeref*(c: var IrStore3, val: IRIndex): IRIndex =
  c.add(IrNode3(kind: ntkDeref, addrLoc: val))

func irParam*(c: var IrStore3, pos: uint32): IRIndex =
  ## A path component. Refers to a parameter
  c.add IrNode3(kind: ntkParam, param: pos.int)

proc irImm*(c: var IrStore3, val: uint32): IRIndex =
  ## Load an immediate int value.
  ## TODO: maybe store the `PNode` in the IR for a `irkConst` instead? And
  ##       move const handling to stage 2?
  c.add(IrNode3(kind: ntkImm, immediate: val))

proc irPathArr*(c: var IrStore3, src: IRIndex, idx: IRIndex): IRIndex =
  ## Path constructor. `src` must be a location or path representing an
  ## array; `idx` must be a value (both literal and run-time value)
  c.add(IrNode3(kind: ntkPathArr, arrSrc: src, idx: idx))

proc irPathObj*(c: var IrStore3, src: IRIndex, idx: int): IRIndex =
  ## Path constructor. `src` must be a location or path representing a
  ## record
  # TODO: `idx` should be a ``uint16``
  c.add(IrNode3(kind: ntkPathObj, objSrc: src, field: idx.int16))

func irConv*(c: var IrStore3, typ: TypeId, val: IRIndex): IRIndex =
  c.add IrNode3(kind: ntkConv, destTyp: typ, srcOp: val)

func irCast*(c: var IrStore3, typ: TypeId, val: IRIndex): IRIndex =
  c.add IrNode3(kind: ntkCast, destTyp: typ, srcOp: val)

proc irAsgn*(c: var IrStore3, kind: AssignKind, path: PathIndex, src: IRIndex): IRIndex {.discardable.} =
  ## Write to a location
  #doAssert c.ops[path].kind in {inktPathObj, inktPathArr, inktPathCall}
  # TODO: declare proper sets and use them here
  #doAssert c.nodes[path].kind in {ntkLoc, ntkPathObj, ntkPathArr, ntkCall}, $c.ops[path].kind
  #doAssert c.nodes[src].kind notin {inktGlobal, inktLocal, inktTemp}
  doAssert path != InvalidIndex
  doAssert src != InvalidIndex
  c.add(IrNode3(kind: ntkAsgn, asgnKind: kind, wrDst: path, wrSrc: src))

func irCall*(c: var IrStore3, callee: IRIndex, numArgs: uint32): IRIndex =
  c.add(IrNode3(kind: ntkCall, ckind: ckNormal, callee: callee, numArgs: numArgs))

func irCall*(c: var IrStore3, callee: BuiltinCall, typ: TypeId, numArgs: uint32): IRIndex =
  c.add(IrNode3(kind: ntkCall, ckind: ckBuiltin, builtin: callee, typ: typ, numArgs: numArgs))

func irCall*(c: var IrStore3, callee: TMagic, typ: TypeId, numArgs: uint32): IRIndex =
  assert callee != mNone
  assert typ != NoneType
  c.add(IrNode3(kind: ntkCall, ckind: ckMagic, magic: callee, typ: typ, numArgs: numArgs))

func irJoinFwd*(c: var IrStore3): JoinPoint =
  ## TODO: document
  ## Helper to make modifications of the IR easier. During IR-gen when the
  ## target is not yet known (e.g. when generating an if-branch)
  result = c.numJoins
  inc c.numJoins

func irLoopJoin*(c: var IrStore3): JoinPoint =
  result = c.numJoins
  let pos = c.add IrNode3(kind: ntkJoin, joinPoint: result)
  inc c.numJoins

func irJoin*(c: var IrStore3, jp: JoinPoint) =
  ## TODO: document
  ## A join point
  let pos = c.add(IrNode3(kind: ntkJoin, joinPoint: jp))

func keys*(x: seq): Slice[int] =
  0..x.high

func irBranch*(c: var IrStore3, cond: IRIndex, target: JoinPoint): IRIndex {.discardable.} =
  ## TODO: document
  ## A branch
  assert target in 0..<c.numJoins
  c.add(IrNode3(kind: ntkBranch, cond: cond, target: target))

func irGoto*(c: var IrStore3, target: JoinPoint): IRIndex {.discardable.} =
  ## TODO: document
  ## Unstructured control-flow.
  c.add(IrNode3(kind: ntkGoto, gotoTarget: target))

func irCont*(c: var IrStore3, target: JoinPoint, then: JoinPoint) =
  discard c.add(IrNode3(kind: ntkGotoCont, contTarget: target, contThen: then))

func irGotoLink*(c: var IrStore3, target: JoinPoint) =
  discard

func irLocal*(c: var IrStore3, name: int): IRIndex =
  ## references a local
  c.add(IrNode3(kind: ntkLocal, local: name))

func irProc*(c: var IrStore3, p: ProcId): IRIndex =
  c.add IrNode3(kind: ntkProc, procId: p)

func irAddr*(c: var IrStore3, loc: IRIndex): IRIndex =
  ## Take the address of a location
  c.add(IrNode3(kind: ntkAddr, addrLoc: loc))

# version 1 (old) transition helpers

func irLit*(c: var IrStore3, lit: Literal): IRIndex =
  #assert n.typ != nil
  result = c.add(IrNode3(kind: ntkLit, litIdx: c.literals.len))
  c.literals.add(lit)

# ------ query procs

func len*(c: IrStore3): int =
  c.nodes.len

func numLocals*(s: IrStore3): int =
  s.locals.len

func numJoins*(ir: IrStore3): int =
  ir.numJoins

func isLastAGoto*(ir: IrStore3): bool =
  ir.nodes.len > 0 and ir.nodes[^1].kind in {ntkGoto, ntkGotoCont}

iterator nodes*(s: IrStore3): lent IrNode3 =
  for it in s.nodes:
    yield it

iterator locals*(s: IrStore3): (TypeId, DeclId) =
  for it in s.locals:
    yield (it.typ, it.decl)

func at*(irs: IrStore3, i: IRIndex): lent IrNode3 =
  irs.nodes[i]

func sym*(c: IrStore3, n: IrNode3): SymId =
  n.sym #c.syms[n.symIdx]

func procId*(n: IrNode3): ProcId =
  n.procId

func paramIndex*(n: IrNode3): int =
  n.param

func getLocal*(irs: IrStore3, n: IRIndex): lent Local =
  irs.locals[irs.nodes[n].local]

func getLocalIdx*(irs: IrStore3, n: IRIndex): int =
  irs.nodes[n].local

func getLit*(irs: IrStore3, n: IrNode3): lent Literal =
  irs.literals[n.litIdx]

func isLoop*(ir: IrStore3, j: JoinPoint): bool =
  false#ir.joins[j][1]

func kind*(n: IrNode3): IrNodeKind3 {.inline.} =
  n.kind

func fieldIdx*(n: IrNode3): int =
  n.field.int

func arrIdx*(n: IrNode3): IRIndex =
  n.idx

func isBuiltIn*(n: IrNode3): bool =
  n.ckind == ckBuiltin

func callKind*(n: IrNode3): CallKind {.inline.} =
  n.ckind

func callee*(n: IrNode3): IRIndex =
  n.callee

func builtin*(n: IrNode3): BuiltinCall =
  n.builtin

func magic*(n: IrNode3): TMagic {.inline.} =
  n.magic

func argCount*(n: IrNode3): int =
  n.numArgs.int

# TODO: rename to `arg` or `getArg`
func args*(ir: IrStore3, n: IRIndex, i: Natural): IRIndex =
  let num = ir.at(n).numArgs.int
  assert i < num
  # the arguments are stored in the nodes coming just before the
  # ``ntkCall`` node
  result = ir.nodes[n - num + i].theLoc

iterator args*(ir: IrStore3, n: IRIndex): IRIndex =
  var i = n - ir.at(n).numArgs.int
  let hi = n
  while i < hi:
    yield ir.nodes[i].theLoc
    inc i

func typ*(n: IrNode3): TypeId =
  ## The return type of a builtin call
  case n.kind
  of ntkCall:
    assert n.ckind in {ckBuiltin, ckMagic}
    n.typ
  of ntkConv, ntkCast:
    n.destTyp
  else:
    unreachable(n.kind)

func asgnKind*(n: IrNode3): AssignKind =
  n.asgnKind


func cond*(n: IrNode3): IRIndex =
  n.cond

func joinPoint*(n: IrNode3): JoinPoint =
  n.joinPoint

func target*(n: IrNode3): JoinPoint =
  case n.kind
  of ntkBranch:
    n.target
  of ntkGoto:
    n.gotoTarget
  else:
    unreachable(n.kind)

func addrLoc*(n: IrNode3): IRIndex =
  n.addrLoc

func wrLoc*(n: IrNode3): IRIndex =
  n.wrDst

func srcLoc*(n: IrNode3): IRIndex =
  let node = n
  case node.kind
  of ntkAsgn:
    node.wrSrc
  of ntkPathObj:
    node.objSrc
  of ntkPathArr:
    node.arrSrc
  of ntkUse, ntkConsume:
    node.theLoc
  of ntkConv, ntkCast:
    node.srcOp
  else:
    unreachable(node.kind)

func mapTypes*(ir: var IrStore3, tg: DeferredTypeGen) =
  for n in ir.nodes.mitems:
    case n.kind
    of ntkCall:
      case n.ckind
      of ckBuiltin, ckMagic:
        if n.typ != NoneType:
          n.typ = tg.map(n.typ)
      of ckNormal: discard
    of ntkCast, ntkConv:
      n.destTyp = tg.map(n.destTyp)
    else:
      discard

  for lit in ir.literals.mitems:
    if lit.typ != NoneType:
      # literals can have a non-placeholder type ID already, so ``maybeMap``
      # is used
      lit.typ = tg.maybeMap(lit.typ)

  for loc in ir.locals.mitems:
    loc.typ = tg.map(loc.typ)

iterator nodes*(x: IrNodes): IRIndex =
  var i = 0
  let L = x.data.len
  while i < L:
    yield IRIndex(i)
    i += cast[IrNodeHdr](x.data[i]).len


# IrCursor interface

type
  SeqAdditions[T] = object
    # TODO: needs a better name
    data: seq[T]
    start: int

type IrCursor* = object
  pos: int
  actions: seq[(bool, Slice[IRIndex])] # true = replace, false = insert
  #newSyms: SeqAdditions[PSym]
  newLocals: SeqAdditions[Local]
  newLiterals: SeqAdditions[Literal] # literal + type
  newNodes: seq[IrNode3]

  traces: seq[seq[StackTraceEntry]]

  nextIdx: IRIndex
  nextJoinPoint: JoinPoint

func add[T](x: var SeqAdditions[T], item: sink T): int {.inline.} =
  result = x.start + x.data.len
  x.data.add(item)

func add[T](x: var SeqAdditions[T], other: openArray[T]) {.inline.} =
  x.data.add(other)

func setFrom[T](x: var SeqAdditions[T], s: seq[T]) =
  # TODO: document
  x.start = s.len

func start[T](x: SeqAdditions[T]): int {.inline.} =
  x.start

func apply[T](dest: var seq[T], src: sink SeqAdditions[T]) =
  # TODO: rename function or swap parameters?
  dest.add(src.data)

func setup*(cr: var IrCursor, ir: IrStore3) =
  cr.nextIdx = ir.len
  cr.nextJoinPoint = ir.numJoins
  #cr.newSyms.setFrom(ir.syms)
  cr.newLocals.setFrom(ir.locals)
  cr.newLiterals.setFrom(ir.literals)

func getNext(cr: var IrCursor): IRIndex {.inline.} =
  result = cr.nextIdx
  inc cr.nextIdx


func setPos*(cr: var IrCursor, pos: IRIndex) {.inline.} =
  cr.pos = pos

func position*(cr: IrCursor): int {.inline.} =
  cr.pos

func replace*(cr: var IrCursor) =
  ## Switches to replace mode. The next insert will overwrite the node at the cursor position
  assert cr.actions.len == 0 or cr.actions[^1][0] == false or cr.actions[^1][1].a != cr.pos, "replace already called"
  cr.actions.add (true, cr.pos .. cr.pos-1)

func insert(cr: var IrCursor, n: sink IrNode3): IRIndex =
  cr.newNodes.add n
  when useNodeTraces:
    {.cast(noSideEffect).}:
      cr.traces.add getStackTraceEntries()

  if cr.actions.len > 0 and cr.actions[^1][1].a == cr.pos:
      # append to the insertion or replacement
      inc cr.actions[^1][1].b
  else:
    cr.actions.add (false, cr.pos..cr.pos)
  result = cr.getNext()

func insertSym*(cr: var IrCursor, sym: SymId): IRIndex =
  assert sym != NoneSymbol
  cr.insert IrNode3(kind: ntkSym, sym: sym)

func insertParam*(cr: var IrCursor, param: Natural): IRIndex =
  cr.insert IrNode3(kind: ntkParam, param: param)

func insertProcSym*(cr: var IrCursor, prc: ProcId): IRIndex =
  cr.insert IrNode3(kind: ntkProc, procId: prc)

func insertArgs(cr: var IrCursor, args: openArray[IRIndex]) =
  for arg in args.items:
    # TODO: using ``ntkUse`` is not correct, but we don't know if it's a
    #       mutating or sink parameter here. The user should be responsible
    #       for setting up the argument list
    discard cr.insert(IrNode3(kind: ntkUse, theLoc: arg))

func insertCallExpr*(cr: var IrCursor, prc: ProcId, args: varargs[IRIndex]): IRIndex =
  let c = cr.insertProcSym(prc)
  cr.insertArgs(args)
  result = cr.insert IrNode3(kind: ntkCall, ckind: ckNormal, callee: c, numArgs: args.len.uint32)

func insertCallStmt*(cr: var IrCursor, prc: ProcId, args: varargs[IRIndex]) =
  discard insertCallExpr(cr, prc, args)

func insertCallExpr*(cr: var IrCursor, callee: IRIndex, args: varargs[IRIndex]): IRIndex =
  cr.insertArgs(args)
  cr.insert IrNode3(kind: ntkCall, ckind: ckNormal, callee: callee, numArgs: args.len.uint32)

func insertCallExpr*(cr: var IrCursor, bc: BuiltinCall, typ: TypeId, args: varargs[IRIndex]): IRIndex =
  cr.insertArgs(args)
  result = cr.insert IrNode3(kind: ntkCall, ckind: ckBuiltin, builtin: bc, typ: typ, numArgs: args.len.uint32)

func insertCallExpr*(cr: var IrCursor, m: TMagic, typ: TypeId, args: varargs[IRIndex]): IRIndex =
  assert m != mNone
  assert typ != NoneType
  cr.insertArgs(args)
  result = cr.insert IrNode3(kind: ntkCall, ckind: ckMagic, magic: m, typ: typ, numArgs: args.len.uint32)

func insertLit*(cr: var IrCursor, lit: Literal): IRIndex =
  cr.insert IrNode3(kind: ntkLit, litIdx: cr.newLiterals.add(lit))

func insertAsgn*(cr: var IrCursor, kind: AssignKind, a, b: IRIndex) =
  discard cr.insert IrNode3(kind: ntkAsgn, asgnKind: kind, wrDst: a, wrSrc: b)

func insertCast*(cr: var IrCursor, t: TypeId, val: IRIndex): IRIndex =
  cr.insert IrNode3(kind: ntkCast, destTyp: t, srcOp: val)

func insertConv*(cr: var IrCursor, t: TypeId, val: IRIndex): IRIndex =
  cr.insert IrNode3(kind: ntkConv, destTyp: t, srcOp: val)

func insertDeref*(cr: var IrCursor, val: IRIndex): IRIndex =
  cr.insert IrNode3(kind: ntkDeref, addrLoc: val)

func insertAddr*(cr: var IrCursor, val: IRIndex): IRIndex =
  cr.insert IrNode3(kind: ntkAddr, addrLoc: val)

func insertPathObj*(cr: var IrCursor, obj: IRIndex, field: int16): IRIndex =
  cr.insert IrNode3(kind: ntkPathObj, objSrc: obj, field: field)

func insertPathArr*(cr: var IrCursor, arr, idx: IRIndex): IRIndex =
  cr.insert IrNode3(kind: ntkPathArr, arrSrc: arr, idx: idx)

func newJoinPoint*(cr: var IrCursor): JoinPoint =
  result = cr.nextJoinPoint
  inc cr.nextJoinPoint

func insertBranch*(cr: var IrCursor, cond: IRIndex, target: JoinPoint) =
  discard cr.insert IrNode3(kind: ntkBranch, cond: cond, target: target)

func insertGoto*(cr: var IrCursor, t: JoinPoint) =
  discard cr.insert IrNode3(kind: ntkGoto, gotoTarget: t)

func insertJoin*(cr: var IrCursor, t: JoinPoint) =
  discard cr.insert IrNode3(kind: ntkJoin, joinPoint: t)

func newLocal*(cr: var IrCursor, kind: LocalKind, t: TypeId, d: DeclId): int =
  assert t != NoneType
  cr.newLocals.add Local(kind: kind, typ: t, decl: d)

func newLocal*(cr: var IrCursor, kind: LocalKind, t: TypeId): int =
  assert kind == lkTemp
  assert t != NoneType
  cr.newLocals.add Local(kind: kind, typ: t)

func insertLocalRef*(cr: var IrCursor, name: int): IRIndex =
  cr.insert IrNode3(kind: ntkLocal, local: name)

func patchIdx(n: var IRIndex, patchTable: seq[IRIndex]) =
  assert patchTable[n] != -1, "node was removed"
  n = patchTable[n]

func patch(n: var IrNode3, patchTable: seq[IRIndex]) =

  template patchIdx(n: var IRIndex) =
    patchIdx(n, patchTable)

  case n.kind
  of ntkCall:
    if n.ckind == ckNormal:
      patchIdx(n.callee)

  of ntkAsgn:
    patchIdx(n.wrDst)
    patchIdx(n.wrSrc)

  of ntkUse, ntkConsume:
    patchIdx(n.theLoc)
  of ntkAddr, ntkDeref:
    patchIdx(n.addrLoc)
  of ntkBranch:
    patchIdx(n.cond)

  of ntkPathObj:
    patchIdx(n.objSrc)
  of ntkPathArr:
    patchIdx(n.arrSrc)
    patchIdx(n.idx)

  of ntkConv, ntkCast:
    patchIdx(n.srcOp)

  of ntkJoin, ntkGoto, ntkSym, ntkLocal, ntkLocEnd, ntkImm, ntkGotoCont,
     ntkContinue, ntkGotoLink, ntkLoad, ntkWrite, ntkRoot, ntkLit, ntkProc,
     ntkParam:
    discard "nothing to patch"

func inline*(cr: var IrCursor, other: IrStore3, sEnv: SymbolEnv, args: varargs[IRIndex]): IRIndex =
  ## Does NOT create temporaries for each arg
  # XXX: unfinished

  # register the insertion
  if cr.actions.len > 0 and cr.actions[^1][1].a == cr.pos:
      # append to the insertion or replacement
      cr.actions[^1][1].b += other.len
  else:
    cr.actions.add (false, cr.pos..(cr.pos+other.len-1))

  let oldLen = cr.newNodes.len

  cr.newNodes.add(other.nodes)
  #cr.newSyms.add(other.syms)
  cr.newLocals.add(other.locals)
  cr.traces.add(other.sources) # use the traces of the original

  var patchTable = newSeq[IRIndex](other.len)

  # search for references to parameters and replace them with the
  # corresponding arg from `args`. Also patch symbol and local references
  for i in oldLen..<cr.newNodes.len:
    patchTable[i - oldLen] = i
    case cr.newNodes[i].kind
    of ntkSym:
      let s = sEnv[cr.newNodes[i].sym]
      # XXX: another indicator that a dedicated ``ntkParam`` would be
      #      better: we need access to ``SymbolEnv`` here
      if s.kind == skParam:
        assert s.position < args.len, "not enough arguments"
        # for simplicity, the original parameter reference node is left as is
        patchTable[i - oldLen] = args[s.position]
      #else:
      #  cr.newNodes[i].symIdx += cr.newSyms.start

    of ntkLocal:
      cr.newNodes[i].local += cr.newLocals.start
    else:
      patch(cr.newNodes[i], patchTable)


func updateV1(ir: var IrStore3, cr: sink IrCursor) =
  ## Integrates the changes collected by the cursor `cr` into `ir`
  # XXX: non-descriptive name
  # XXX: superseded and now unused
  var patchTable: seq[IRIndex]
  let oldLen = ir.len
  patchTable.newSeq(cr.nextIdx) # old ir len + insert node count

  #ir.syms.apply(cr.newSyms)
  ir.locals.apply(cr.newLocals)
  ir.literals.apply(cr.newLiterals)

  var currOff = 0
  var p = 0
  var p1 = 0
  var np = 0

  func process(ir: var IrStore3, p: var int, next: int) =
    while p < next:
      patchTable[p] = p + currOff
      patch(ir.nodes[p + currOff], patchTable)
      inc p

  while p1 < cr.actions.len:
    let (kind, slice) = cr.actions[p1]
    process(ir, p, slice.a)

    template insertNode(p: int) =
      patchTable[oldLen + np] = p
      ir.nodes.insert(cr.newNodes[np], p)

      when useNodeTraces:
        ir.sources.insert(cr.traces[np], p)

      patch(ir.nodes[p], patchTable)

    if kind: # replace
      assert slice.len > 0
      patchTable[slice.a] = slice.b + currOff # the replaced node
      for i in slice.a..<slice.b:
        let pos = i + currOff
        insertNode(pos)
        inc np

      # replace the node
      ir.nodes[slice.b + currOff] = cr.newNodes[np]
      when useNodeTraces:
        ir.sources[slice.b + currOff] = cr.traces[np]
      inc np

      # patch the replaced node
      patch(ir.nodes[slice.b + currOff], patchTable)

      currOff += slice.len - 1

      # we replaced a node, prevent it from being included in `process`
      inc p
    else: # insert
      for i in slice:
        let pos = i + currOff
        insertNode(pos)
        inc np

      currOff += slice.len

    inc p1

  if p < oldLen:
    # patch the remaining nodes
    process(ir, p, oldLen)

func moveMem[T](dst: var openArray[T], dstP, srcP: int, len: int) =
  assert srcP + len <= dst.len
  assert dstP + len <= dst.len
  moveMem(addr dst[dstP], addr dst[srcP], len * sizeof(T))

func copyMem[T](dst: var openArray[T], src: openArray[T], dstP, srcP: int, len: int) =
  assert srcP + len <= src.len
  assert dstP + len <= dst.len
  copyMem(addr dst[dstP], unsafeAddr src[srcP], len * sizeof(T))

func zeroMem[T](dst: var openArray[T]) =
  if dst.len > 0:
    zeroMem(addr dst[0], sizeof(T) * dst.len)

func update*(ir: var IrStore3, cr: sink IrCursor) =
  ## Integrates the changes collected by the cursor `cr` into `ir`
  # XXX: non-descriptive name

  if cr.newNodes.len == 0:
    return

  var patchTable: seq[IRIndex]
  let oldLen = ir.len
  patchTable.newSeq(cr.nextIdx) # old ir len + insert node count

  #ir.syms.apply(cr.newSyms)
  ir.locals.apply(cr.newLocals)
  ir.literals.apply(cr.newLiterals)
  ir.numJoins = cr.nextJoinPoint

  let start = cr.actions[0][1].a

  var numNew = 0
  for kind, slice in cr.actions.items:
    if kind:
      numNew += slice.len - 1
    else:
      numNew += slice.len

  ir.nodes.setLen(oldLen + numNew)
  when useNodeTraces:
    ir.sources.setLen(oldLen + numNew)

  let L = oldLen - start
  moveMem(ir.nodes, ir.nodes.len - L, start, L)
  when useNodeTraces:
    moveMem(ir.sources, ir.sources.len - L, start, L)

  var copySrc = ir.nodes.len - L # where to take
  var p = start # the position in the old node buffer where we're at
  var insert = start # where to insert the next nodes
  var np = 0 # the read position in the newNodes buffer

  # fill the patchTable for the nodes that aren't moved
  for i in 0..<start:
    patchTable[i] = i

  for i, (kind, slice) in cr.actions.pairs:
    copyMem(ir.nodes, cr.newNodes, insert, np, slice.len)
    when useNodeTraces:
      copyMem(ir.sources, cr.traces, insert, np, slice.len)

    for j in 0..<slice.len:
      patchTable[oldLen + np] = insert + j
      inc np

    if kind: # replace
      patchTable[p] = insert + slice.len - 1 # the replaced node

      # we replaced a node, prevent it from being included in the following move
      inc p
      inc copySrc

      assert copySrc >= insert + slice.len

    else: # insert
      discard

    inc insert, slice.len

    let
      next = (if i+1 < cr.actions.len: cr.actions[i+1][1].a else: oldLen)
      num = next - p # number of elements to move
    # regions can overlap -> use ``moveMem``
    assert num >= 0
    moveMem(ir.nodes, insert, copySrc, num)
    when useNodeTraces:
      moveMem(ir.sources, insert, copySrc, num)

    let start = p
    while p < next:
      patchTable[p] = insert + (p - start)
      inc p

    copySrc += num
    insert += num

  # we've effectively done a ``move`` for all elements so we have to also zero
  # the memory or else the garbage collector would clean up the traces
  when useNodeTraces:
    zeroMem(cr.traces)

  # patch the node indices
  for i, n in ir.nodes.mpairs:
    patch(n, patchTable)