## Implements a user-driven continuation-passing-style transformation.
## In summary, a procedure is split into multiple continuations,
## with yields turned into a call of the `cpsMagic` procedure with the
## next continuation to run passed along.

type
  LabelId = int
  ContId = int

  TransformCtx = object
    labels: Table[LabelId, ContId]
      ## associates each label with the continuation it belongs to
    next: ContId
      ## provides the next ID to use

    fields: seq[PSym]
      ## the make-up of the lifted environment
    lifted: Table[int, int]
      ## the locals that are lifted into the environment. sym ID -> index
      ## into fields

    self: PSym ## the self parameter
    typ: PType ## the type of the self parameter

proc propagate(tree: MirTree, c: var TransformCtx) =
  ## Computes how many continuations are needed and assigns the ID of the
  ## belonging-to continuation to each label.
  ##
  ## We perform abstract execution of the instructions. A yield starts
  ## a new continuation, and if a label is reached from two different
  ## continuations, it needs to start a new continuation too.
  var pc = 0
  var curr = c.nextId ## the ID of the active continuation
  inc c.nextId

  var marker: IntSet
    ## labels that were alrady marked as the start of a new
    ## continuation. Used to prevent labels from starting new continuation
    ## multiple times
  var loops: Table[LabelId, int]
  var exits: Table[LabelId, seq[int]] ## the stack of continuations for the finalizer
                                      ## handling

  template disable() =
    curr = -1

  proc setLabel(c: var TransformCtx, label: LabelId, curr: ContId; force=false) =
    if label in c.labels or (curr != -1 and force):
      # XXX: don't capture `marker`
      if force or c.labels[label] != cur:
        if marker.containsOrIncl():
          c.labels[node.label] = c.nextId
          inc c.nextId

    elif curr != -1:
      if force:
        c.labels[node.label] = curr

      c.labels[node.label] = curr

  # pre-pass: collect all finalizer/cleanup exits
  pc = 0
  while pc < tree.len:
    case tree[pc].kind
    of mnkGotoCleanup, mnkGotoFinalizer:
      var prev = -1
      while tree[pc].kind in Gotos:
        case tree[pc].kind
        of mnkGotoCleanup, mnkGotoFinalizer:
          if prev != -1:
            # TODO: ensure that a table entry actually exists
            exits[prev].add tree[pc].label
          prev = tree[pc].label
        of mnkGoto: # chain exit
          if prev != -1:
            exits[prev].add tree[pc].label
        else:
          unreachable()
    else:
      discard

    inc pc

  # main pass: compute for each label which continuation it belongs to. Each
  # loop instruction is taken at most *once*.
  pc = 0
  while pc < tree.len:
    let node {.cursor.} = tree[pc]
    case node.kind
    of mnkGoto, mnkBranch:
      setLabel(c, node.label, curr)
      disable()
    of mnkIf, mnkIfError:
      setLabel(c, node.label, curr)
    of mnkLoop:
      setLabel(c, node.label, curr)
      # if the label is not in the table, it means the loop was either:
      # 1. visited already
      # 2. visited during a disabled run
      if pop(loops, node.label, pc):
        curr = c.labels[node.label]
    of mnkGotoCleanup, mnkGotoFinalizer:
      # skip the goto chain:
      while tree[pc].kind in Gotos:
        inc pc

      # only set the associated continuation for the first target in the
      # chain
      setLabel(c, node.label, curr)
      disable()
    of mnkLabel:
      if node.label in labels:
        let next = labels[node.label]
        if curr == -1:
          # the previous code was disabled
          curr = next
        elif next != curr:
          # the label is reached from two different continuations -> a new
          # continuation is required
          labels[node.label] = nextId
          curr = nextId
          inc nextId

      elif curr != -1:
        # this must be a loop label that is visited for the first time
        labels[node.label] = curr
        loops[node.label] = pc
        # disable during the first traversal; we need to make sure that
        disable()
    of mnkResume:
      # a resume is one-to-many control-flow (a cleanup/finalizer is
      # essentially >-< control-flow). If the cleanup/finalizer section
      # starts a continuation itself or if the resume is not part of the
      # same continuation as the start of the section, each basic block the
      # resume targets is forced to start a new continuation too
      # NOTE: resume control-flow is forward-only, meaning that no loops
      # can be introduced here
      let force = node.label in markers or curr != node.label
      for it in exits[node.label].items:
        setLabel(c, it, curr, force)

      disable()
    of mnkYield:
      # a yield also starts a new continuation
      if pc notin c.nextForYield:
        curr = c.nextId
        inc c.nextId
        c.nextForYield[pc] = curr
      else:
        curr = c.nextForYield[pc]

    of AllNodeKinds - ControlFlowNodes:
      discard

    inc pc

proc root(tree: MirTree, n: NodePosition): NodePosition =
  var n = n
  while tree[n].kind == mnkPath:
    n = tree.operand(n)

proc setupProcs(c: var TransformCtx, tree: MirTree) =
  c.syms.setLen(c.next)
  for i, it in c.syms.mpairs:
    # setup the procedures
    it = newSym(#[...]#)

  # XXX: cleanup-only continuations should be eliminated here

proc accessNext(bu: var MirBuilder, c: TransformCtx): EValue =
  ## Emits the selector for the variable storing the next continuation
  ## to run.
  discard

proc accessEnvField(bu: var MirBuilder, c: TransformCtx, field: PSym): EValue =
  ## Emits the selector for `field`.
  discard

proc check(c: TransformCtx, tree: MirTree, start: ContId, val: OpValue, user: NodePosition): bool =
  ## Tests whether `val` is used across continuations.
  if user == NodePosition(val) + 1:
    # common case
    return false

  # compute which continuation the user is part of:
  var i = val.NodePosition
  var curr = start
  while i < user:
    case tree[i].kind
    of mnkLabel:
      curr = c.labels.getOrDefault(tree[i].label, -1)
    of mnkYield:
      curr = c.nextForYield[i]
    of Gotos:
      curr = -1
    else:
      discard
    inc i

  assert curr != -1, "ill-formed MIR code"
  result = start != cur

proc firstPass(tree: MirTree, c: var TransformCtx, lifted: var IntSet) =
  ## Runs the first pass of the transformation. It:
  ## 1. lifts locals used in two different continuations
  ## 2. materializes temporaries for reads crossing continuations
  ##
  ## This prepares the the continuations for being re-ordered or separated.
  var i = 0
  var curr: ContId = 0
  var locals: Table[int, ContId]
    ## associates locals with their defined-in continuation

  while i < tree.len:
    let node {.cursor.} = tree[i]
    case node.kind
    of mnkLabel:
      curr = labels[node.label]

      if curr == -1:
        # don't touch code part of inactive basic blocks, skip to
        # the next label or yield
        inc i
        while tree[i].kind notin {mnkLabel, mnkYield}:
          inc i

        dec i # undo the following increment
    of ImplicitMaterialize + {mnkMaterialize, mnkMaterializeL}:
      let user = tree.user(i)
      if c.check(tree, i, user):
        let useAddr = tree[i].kind == mnkMaterializeL
        let field = addTemp(env, tree[i].typ, useAddr)
        changes.seek(i)
        changes.injectSink(buf):
          # first assign the value to the lifted temporary
          if useAddr:
            # take the address of the operand
            buf.asgn(
              buf.accessEnvField(c, field),
              buf.paramRef(0, tree[i].typ) => addrOp(field.typ))
          else:
            buf.asgn(
              buf.accessEnvField(c, field),
              buf-paramRef(0, tree[i].typ))

        # then, at the point of use, inject a read of the temporary. In the
        # end, the transformation looks like this:
        #   let _1 = call ...
        #   ....
        #   yield
        #   ...
        #   let _2 = _1.x
        # -->
        #   let _1 = call ...
        #   env.tmp = _1
        #   ...
        #   yield
        #   ...
        #   let _2 = env.tmp.x
        changes.seek(user)
        changes.intercept(buf):
          if useAddr:
            chain(buf, buf.accessEnvField(c, field) => derefOp(tree[i].typ))
          else:
            chain(buf, buf.accessEnvField(c, field))

    of DefNodes:
      if tree[pc + 1].kind == mnkLocal:
        locals[tree[pc + 1].sym.id] = curr

    of UseContext:
      if tree[root(tree, n)].kind == mnkLocal and locals[tree[n].sym.id] != curr:
        # a local is used outside of its defined-in continuation -> lift into
        # the environment if it wasn't already
        if tree[n].sym.id notin c.lifted:
          c.lifted[tree[n].sym.id] = newField(c, tree[n].typ)

    else:
      discard

proc secondPassCps(c: var TransformCtx, tree: MirTree, changes: var Changeset, id: ContId) =
  ## Cull everything not part of the continuation `id` and replace all exits
  ## with returning the next continuation. This is specific to the
  ## language-level CPS support.
  proc exit(bu: var MirBuilder, c: TransformCtx, id: ContId) =
    bu.asgn(
      bu.accessNext(c),
      chain(bu, procLit(c.syms[id])))
    bu.returnStmt()

  proc skip(c: TransformCtx, start: NodePosition, id: ContId, changes: var Changeset): NodePosition {.nimcall.} =
    # skip to the next code part of the selected continuation
    var i = start
    while i < node.len:
      case node[i].kind
      of mnkLabel:
        if c.labels[node.label] == id:
          break
      of mnkYield:
        if c.nextForYield[i] == id:
          break
      else:
        discard
      inc i

    changes.removeRange(start, i - 1)
    result = i

  var i = skip(c, NodePosition 0, id, changes)

  while i < tree.len:
    let node {.cursor.} = tree[i]
    var doSkip = false

    case node.kind
    of mnkLabel:
      if c.labels[node.label] != id:
        # a label that marks the start of different continuation, keep the
        # label and insert an exit after it
        changes.seek(i + 1)
        changes.insert(buf):
          exit(buf, c, c.labels[node.label])

        doSkip = true

    of mnkGoto:
      if labels[node.label] != curr:
        # control-flow from one continuation into another -> replace with exit
        changes.seek(i)
        changes.replace(buf):
          exit(buf, c, c.labels[node.label])

        doSkip = true

    of mnkGotoCleanup, mnkGotoFinalizer:
      if labels[node.label] != curr:
        changes.seek(i)
        changes.replace(buf):
          var j = i
          var prev = PSym(nil)
          while tree[j].kind in Gotos:
            case tree[j].kind
            of mnkGotoCleanup, mnkGotoFinalizer:
              if prev != nil:
                # set the continuation for the cleanup/finalizer block:
                buf.asgn(
                  buf.accessEnvField(c, prev),
                  buf.procLit(c.syms[c.labels[node.label]]))

              if node.label notin c.nextProcs:
                c.nextProcs[node.label] = addTemp(c, c.typ)

              prev = c.nextProcs[node.label]
            of mnkGoto:
              buf.asgn(
                buf.accessEnvField(c, prev),
                buf.procLit(c.syms[c.labels[node.label]]))
            else:
              unreachable()
            inc j

          exit(buf, c, labels[node.label])

    of mnkYield:
      # -->
      #  return cpsMagic(arguments)
      changes.seek(i)
      changes.replaceRaw(buf):
        region(buf, builder):
          # forward the existing arguments:
          var args = newSeq[MirArg](numArgs(tree, i) + 1)
          for j, pos, kind in arguments(tree, i):
            args[j] = arg(buf, kind, pos)

          # pass along the yield's contiuation:
          args[j] = byVal(buf, procLit(c.syms[c.nextForYield[i]]))
          buf.call(args)

        buf.returnStmt()

      doSkip = true
    of mnkResume:
      if node.label in c.nextProcs:
        # the resume uses a procedure indirection
        changes.seek(i)
        changes.replace(buf):
          buf.asgn(
            buf.accessResult(c),
            buf.accessEnvField(c, c.nextProcs[node.label]))

          buf.returnStmt()

        doSkip = true
    else:
      discard

    inc i
    if doSkip:
      skip(c, i, id, changes)

proc thirdPass(tree: MirTree, c: var TransformCtx, changes: var Changeset) =
  ## Rewrites uses of locals that were lifted into the environment.
  var map: Table[int, PSym]
  for i, node in tree.pairs:
    case node.kind
    of DefNodes:
      if tree[i + 1].kind != mnkLocal or tree[i + 1].sym.id notin lifted:
        continue

      let f = c.lifted[tree[i + 1].sym.id]

      if hasInput(tree, buf):
        # replace with an assignment
        changes.replace(buf):
          buf.initAsgn(
            buf.accessEnvField(c, f),
            buf.paramRef(0, f.typ))
      else:
        # no initializer exists. Replace with assigning the default value
        changes.replace(buf):
          buf.initAsgn(
            buf.accessEnvField(c, f),
            buf.magicCall(mDefault, f.typ))

    of mnkLocal:
      # note: this transformation relies on the materializing instruction
      # to immediately follow the selector
      if n.sym.id in lifted:
        changes.replace(buf):
          eval(buf, buf.accessEnvField(c, f))

    else:
      discard "nothing to do"

proc apply(changes: sink Changeset, tree: var MirTree, src: var SourceMap) =
  let p = prepare(changes, src)
  updateSourceMap(source, p)
  apply(tree, p)

proc transform(tree: MirTree, src: SourceMap, prc: PSym): seq[tuple[p: PSym, body: MirBody]] =
  ## The entry point. Produces a list of procedures, each representing a
  ## continuation.
  var c: TransformCtx
  propagate(c, tree)
  setupProcs(c, tree)

  if c.syms.len > 0 and resultPos > prc.ast.len and prc.ast[resultPos] != nil:
    # mark the result variable as lifted into the environment
    let res = prc.ast[resultPos].sym
    c.lifted[res.id] = newField(c, res)

  var
    tree = tree
    src = src

  # apply the transformations for preparing the code for split up:
  var changes = initChangeset(tree)
  firstPass(tree, c, changes)
  apply(changes, tree, src)

  # now extract the bodies:
  result.newSeq(c.syms.len)
  for i, it in c.syms.pairs:
    changes = initChangeset(tree)
    secondPass()
    # TODO: a version of 'apply' that creates a new tree is required
    # apply the
    thirdPass()

    result[i] = (it, body)

  # we're done with the transformations, the only thing left to do
  # is setting finishing the type
  # ....