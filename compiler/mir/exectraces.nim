## Implements a MIR pass that injects calls to the execution-trace procedures
## part of the compiler's run-time.
##
## A call to ``traceEnter`` is injected at the start of a procedure.
## A call to ``traceStep`` is injected at the start of a basic block

import
  compiler/ast/[ast_types, ast],
  compiler/ast/lineinfos,
  compiler/modules/[modulegraphs, magicsys],
  compiler/mir/[mirconstr, mirtrees, mirchangesets, sourcemaps],
  compiler/utils/containers

type
  TraceId* = distinct uint32
  TraceDb* = object
    locations*: Store[TraceId, TLineInfo]
      ## the source location associated with each trace ID

func seekToInsert(code: MirTree, start: NodePosition): NodePosition =
  result = start
  while code[result].kind in {mnkStmtList, mnkScope}:
    inc result

func insertTraceCall(buf: var MirNodeSeq, db: var TraceDb, info: TLineInfo, prc: PSym, voidTy: PType) =
  ## Creates a trace instance, associates it with `info`, and registers it
  ## with `db`. The ID of the resulting trace is used as the argument to the
  ## injected cal to `prc`. `prc` is expected to be a procedure with a single
  ## ``uint32`` parameter and no return value
  assert prc != nil
  let id = db.locations.add(info)
  argBlock(buf):
    buf.add MirNode(kind: mnkProc, sym: prc)
    buf.add MirNode(kind: mnkArg)
    let lit = newIntNode(nkIntLit, id.int)
    lit.typ = prc.typ[1]
    buf.add MirNode(kind: mnkLiteral, lit: lit, typ: lit.typ)
    buf.add MirNode(kind: mnkArg)

  buf.add MirNode(kind: mnkCall, typ: voidTy)
  buf.add MirNode(kind: mnkVoid)

proc insertTraceCalls*(tree: MirTree, sourceMap: SourceMap, db: var TraceDb,
                       enter, step: PSym, voidTy: PType): Changeset =
  result = initChangeset(tree)

  var i = NodePosition 0

  template src(i: NodePosition): TLineInfo =
    sourceFor(sourceMap, NodeInstance i).info

  template insertTraceCall(p: NodePosition, prc: PSym) =
    result.insert(NodeInstance p, buf):
      insertTraceCall(buf, db, src(p), prc, voidTy)

  result.seek seekToInsert(tree, i)
  insertTraceCall(i, enter)

  while i < tree.len.NodePosition:
    let n {.cursor.} = tree[i]

    case n.kind
    of mnkDef:
      # uninteresting -> skip child nodes
      i = sibling(tree, i)
    of mnkCall:
      # XXX: if the call doesn't return normally (i.e. is marked as
      #      ``.noreturn``), the step call that is inserted here will never be
      #      reached
      # TODO: whether a call doesn't return needs to be tracked in the MIR
      #       somehow
      if geRaises notin n.effects:
        # the call doesn't raise, no need to insert a trace step
        discard
      if n.typ.kind == tyVoid:
        result.seek i+2
        result.insert(NodeInstance i+2, buf):
          insertTraceCall(buf, db, src(i+2), step, voidTy)

      else:
        let tmp = result.getTemp()
        result.seek i+1
        result.insert(NodeInstance i+1, buf):
          buf.subTree MirNode(kind: mnkDef):
            buf.add MirNode(kind: mnkTemp, temp: tmp, typ: n.typ)

          insertTraceCall(buf, db, src(i+1), step, voidTy)

          buf.add MirNode(kind: mnkTemp, temp: tmp, typ: n.typ)

      inc i
    of mnkIf:
      # insert a step call before the first statement:
      result.seek seekToInsert(tree, i+1)
      insertTraceCall(i+1, step)
      inc i
    of mnkBranch:
      int32(i) += n.len.int32 # skip the labels
      # insert a step call before the first statement part of the branch:
      result.seek seekToInsert(tree, i+1)
      insertTraceCall(i+1, step)
      inc i
    of mnkRepeat:
      result.seek seekToInsert(tree, i+1)
      insertTraceCall(i+1, step)
      inc i
    of mnkFinally:
      result.seek seekToInsert(tree, i+1)
      insertTraceCall(i+1, step)
      inc i
    of mnkEnd:
      if n.start in {mnkIf, mnkCase, mnkTry, mnkRepeat, mnkBlock}:
        # insert a step call *after* the end node:
        result.seek seekToInsert(tree, i+1)
        insertTraceCall(i+1, step)

      inc i
    else:
      inc i

proc applyPass*(graph: ModuleGraph, tree: var MirTree, sourceMap: var SourceMap,
                db: var TraceDb) =
  ## Injects the trace calls into `tree`. Updates `db` with the added
  ## ``TraceId``s.
  let
    enter = getCompilerProc(graph, "traceEnter")
    step = getCompilerProc(graph, "traceStep")

  assert enter != nil and step != nil, "required compilerprocs are missing"

  let changeset = prepare(insertTraceCalls(tree, sourceMap, db, enter, step, graph.getSysType(unknownLineInfo, tyVoid)),
                          sourceMap)
  updateSourceMap(sourceMap, changeset)
  apply(tree, changeset)