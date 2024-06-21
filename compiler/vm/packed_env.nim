## This module contains the type definitions for a packed representation of
## all the state required for loading and running a standalone VM instance.
##
## In addition, procedures for storing and loading the original objects to and
## from the packed environment object are also located here.
##
## For reading and writing `PackedEnv` to files, a ``rodfile``-based solution
## is provided.
##
## First collecting/packing into a data structure that is then written to disk
## in a separate is not as resource efficient (both in terms of memory
## consumption and time) as doing both steps in a combined manner. The first
## (and current) approach is less complex however, which is why it's chosen
## over the latter.

import
  std/[
    tables
  ],
  compiler/ast/[
    ast_query,
    ast_types,
    lineinfos,
    types
  ],
  compiler/front/[
    options
  ],
  compiler/ic/[
    bitabs,
    rodfiles
  ],
  compiler/mir/[
    mirtrees,
    mirtypes
  ],
  compiler/utils/[
    idioms,
    int128,
    pathutils # for `AbsoluteFile`
  ],
  compiler/vm/[
    identpatterns,
    vmdef,
    vmtypes
  ]

export RodFileError

type
  PackedDataKind* = enum
    pdkInt
    pdkIntLit ## an embedded literal
    pdkFloat
    pdkString
    pdkPtr # also includes ref
    pdkObj
    pdkArray
    pdkSet
    pdkField

  # XXX: `PackedDataNode` is memory-usage wise quite inefficient. Not only at
  #      the layout level (3 out of it's 8 bytes are wasted for padding), but
  #      also for representing data in general. For example: `array[256, byte]`
  #      requires 2048 bytes!
  #      A possible different approach: store the data in it's
  #      raw-byte-serialized representation, with additional metadata
  #      describing where strings and seqs (i.e. values with non-automatic
  #      storage) should be placed. Maybe also only store the non-zero parts
  PackedDataNode* = object
    ## A single node in a depth-first linear tree that is meant for storing
    ## complex data. If a node has children, they follow directly after their
    ## parent node. `PackedDataNode` can be seen as a specialized
    ## version of `PackedNodeLite`
    kind*: PackedDataKind
    pos*: uint32 ## for {pdkInt, pdkFloat, pdkString}: the respective `LitId`
                 ## for {pdkObj, pdkArray, pdkSet}: the number of children
                 ## for pdkPtr: `0` if nil, `1` otherwise
                 ## for `pdkField`: the field's position
                 ## for `pdkIntLit`: a direct literal that fits into 4 byte

  # XXX: the rodfile interface for `BiTable`s stores both `keys` and `values`,
  #      even though `keys` can be reconstructed during loading (at least in
  #      our use-case here). This makes the resulting file larger than
  #      necessary

  PackedEnv* = object
    ## Represents the packed content of a ``VmEnv``, ready to be serialized to
    ## some byte stream.
    strings*: BiTable[string]
    numbers*: BiTable[BiggestInt] # also includes floats

    files*: seq[string]
    infos*: BiTable[TLineInfo]
    dbgSyms*: seq[tuple[name, info: LitId]] # for debugging only

    # content that's largely the same as the corresponding ``VmEnv`` data:
    code*: seq[TInstr]
    debug*: seq[uint32]
      ## packed instruction origin information. Values are indices into
      ## `infos`
    ehTable*: seq[HandlerTableEntry]
    ehCode*: seq[EhInstr]
    consts*: seq[VmConstant]
    procs*: seq[ProcEntry]
    types*: VmTypeEnv

    nodes*: seq[PackedDataNode]
      ## data description. Data is stored as construction expressions, not
      ## as raw binary data
    data*: seq[tuple[typ: VmTypeId, packedId: uint32]]
      ## typed constant data
    globals*: seq[VmTypeId]
      ## types of all globals
    callbacks*: Patterns

    entryPoint*: FunctionIndex

  DataEncoder* = object
    ## Contextual state needed for turning data `PNode`-trees into
    ## `PackedDataNode` trees and storing them into the packed environment
    config*: ConfigRef
    types*: ptr TypeEnv
      # HACK: some parts of constant data encoding need read-only access to
      #       the type environment, so a pointer to the environment is stored
      #       here to prevent excessive parameter passing. No access to the
      #       type environment should be required
    i: int ## the index in `PackedEnv.nodes` where the next item is to be stored

# -------- general utilities ---------------------------------------------

func growBy[T](x: var seq[T], n: Natural) {.inline.} =
  x.setLen(x.len + n)

iterator lpairs[T](x: openArray[T]): tuple[key: int, val: lent T] =
  ## Custom `pairs` iterator that uses `lent`. As of this comment, the stdlib
  ## one doesn't
  var i = 0
  let L = x.len
  while i < L:
    yield (i, x[i])
    inc i

template mapList*[D, S](d: seq[D], s: openArray[S], it: untyped, code) =
  ## `s` and `d` get evaluated multiple times, so beware
  bind lpairs
  d.newSeq(s.len)
  for i, it {.inject.} in lpairs(s):
    d[i] = code

# -------- accessors and shortcuts ---------------------------------------

func getLitId(e: var PackedEnv, x: string): LitId {.inline.} =
  e.strings.getOrIncl(x)

func getLitId(e: var PackedEnv, x: BiggestInt): LitId {.inline.} =
  e.numbers.getOrIncl(x)

func getLitId(e: var PackedEnv, x: BiggestFloat): LitId {.inline.} =
  e.numbers.getOrIncl(cast[BiggestInt](x))

func getInt(e: PackedEnv, n: MirNode): Int128 =
  case n.kind
  of mnkIntLit:
    toInt128 e.numbers[n.number.LitId]
  of mnkUIntLit:
    toInt128 cast[BiggestUInt](e.numbers[n.number.LitId])
  else:
    unreachable()

# -------- data storing --------------------------------------------------

func startEncoding*(enc: var DataEncoder, e: PackedEnv) {.inline.} =
  enc.i = e.nodes.len

func put(enc: var DataEncoder, e: var PackedEnv,
         d: sink PackedDataNode) {.inline.} =
  e.nodes[enc.i] = d
  inc enc.i

func storeDataNode(enc: var DataEncoder, e: var PackedEnv,
                   t: MirTree, n: NodePosition)
  ## Stores in `e.nodes` the data represented by the MIR constant expression
  ## `t`. The caller is responsible for making sure that there's a slot
  ## allocated in `e.nodes` for the top data-node. Space allocation for the
  ## sub-data-nodes is handled by ``storeData``.

proc storeFieldsData(enc: var DataEncoder, e: var PackedEnv,
                     t: MirTree, n: NodePosition) =
  let
    typ = enc.types[][t[n].typ]
    count = t[n].len
  enc.put e, PackedDataNode(kind: pdkObj, pos: count.uint32)
  e.nodes.growBy(count * 2) # make space for the content

  # iterate over all fields in the construction and pack and store them:
  var n = n + 1
  for _ in 0..<count:
    inc n # skip the binding node
    let s = lookupInType(typ, t[n].field.int) ## the field symbol
    inc n # move the cursor to the field's data

    enc.put e, PackedDataNode(kind: pdkField, pos: s.position.uint32)
    enc.storeDataNode(e, t, n+1)

    n = t.sibling(n) # move the cursor to the next field

proc storeTupleData(enc: var DataEncoder, e: var PackedEnv,
                    t: MirTree, n: NodePosition) =
  let count = t[n].len
  enc.put e, PackedDataNode(kind: pdkObj, pos: count.uint32)
  e.nodes.growBy(count * 2) # make space for the content

  # pack and store all elements:
  var n = n + 1
  for i in 0..<count:
    enc.put e, PackedDataNode(kind: pdkField, pos: i.uint32)
    enc.storeDataNode(e, t, n+1)
    n = t.sibling(n)

proc storeArrayData(enc: var DataEncoder, e: var PackedEnv,
                    t: MirTree, n: NodePosition) =
  let count = t[n].len
  enc.put e, PackedDataNode(kind: pdkArray, pos: count.uint32)
  e.nodes.growBy(count) # make space for the content

  # encode all elements:
  var n = n + 1
  for _ in 0..<count:
    enc.storeDataNode(e, t, n+1)
    n = t.sibling(n)

proc storeSetData(enc: var DataEncoder, e: var PackedEnv,
                  t: MirTree, n: NodePosition) =
  let
    count = t[n].len
    typ = enc.types[][t[n].typ]
  enc.put e, PackedDataNode(kind: pdkSet, pos: count.uint32 * 2)
  e.nodes.growBy(count * 2) # make space for the content

  template adjusted(n: MirNode, typ: PType): uint32 =
    # make the range start at zero
    toUInt32(e.getInt(n) - firstOrd(enc.config, typ))

  var n = n + 1
  # bitsets only store values in the range 0..high(uint16), so the values can
  # be stored directly
  for _ in 0..<count:
    if t[n].kind == mnkRange:
      enc.put e, PackedDataNode(kind: pdkIntLit, pos: adjusted(t[n + 1], typ))
      enc.put e, PackedDataNode(kind: pdkIntLit, pos: adjusted(t[n + 2], typ))
    else:
      let d = PackedDataNode(kind: pdkIntLit, pos: adjusted(t[n], typ))
      enc.put e, d
      enc.put e, d

    n = t.sibling(n)

func storeDataNode(enc: var DataEncoder, e: var PackedEnv,
                   t: MirTree, n: NodePosition) =
  case t[n].kind
  of mnkNilLit:
    if enc.types[][t[n].typ].skipTypes(abstractInst).callConv == ccClosure:
      # XXX: some unexpanded `nil` closure literals reach here, so we have
      #      to expand them here. This needs to happen earlier
      enc.put e, PackedDataNode(kind: pdkObj, pos: 2)
      e.nodes.growBy(4)
      enc.put e, PackedDataNode(kind: pdkField, pos: 0)
      enc.put e, PackedDataNode(kind: pdkPtr, pos: 0)
      enc.put e, PackedDataNode(kind: pdkField, pos: 0)
      enc.put e, PackedDataNode(kind: pdkPtr, pos: 0)
    else:
      enc.put e, PackedDataNode(kind: pdkPtr, pos: 0)
  of mnkIntLit, mnkUIntLit:
    enc.put e, PackedDataNode(kind: pdkInt, pos: t[n].number.uint32)
  of mnkFloatLit:
    enc.put e, PackedDataNode(kind: pdkFloat, pos: t[n].number.uint32)
  of mnkStrLit:
    # the ID indexes into the string BiTable, it can be packed directly
    enc.put e, PackedDataNode(kind: pdkString, pos: t[n].strVal.uint32)
  of mnkProcVal:
    # the ID is stable, it can be packed directly
    enc.put e, PackedDataNode(kind: pdkIntLit, pos: t[n].prc.uint32)
  of mnkArrayConstr, mnkSeqConstr:
    enc.storeArrayData(e, t, n)
  of mnkTupleConstr, mnkClosureConstr:
    enc.storeTupleData(e, t, n)
  of mnkSetConstr:
    enc.storeSetData(e, t, n)
  of mnkObjConstr, mnkRefConstr:
    enc.storeFieldsData(e, t, n)
  else:
    unreachable(t[n].kind)

func storeData*(enc: var DataEncoder, e: var PackedEnv, tree: MirTree): int =
  ## Packs the MIR constant expression `tree` and puts it into `e`. Returns
  ## the index of the top data node.
  result = enc.i
  e.nodes.growBy(1)
  storeDataNode(enc, e, tree, NodePosition 0)

func getIntVal*(pe: PackedEnv, n: PackedDataNode): BiggestInt {.inline.} =
  case n.kind
  of pdkInt:    pe.numbers[n.pos.LitId]
  of pdkIntLit: n.pos.BiggestInt
  else:         unreachable(n.kind)

func getFloatVal*(pe: PackedEnv, n: PackedDataNode): BiggestFloat {.inline.} =
  assert n.kind == pdkFloat
  cast[BiggestFloat](pe.numbers[n.pos.LitId])

func storeDbgSym(dst: var PackedEnv, sym: PSym): uint32 =
  let
    info = dst.infos.getOrIncl(sym.info)
    name = dst.strings.getOrIncl(sym.name.s)

  result = dst.dbgSyms.len.uint32
  dst.dbgSyms.add((name: name, info: info))

proc loadFileInfos*(c: ConfigRef, frm: PackedEnv) =
  ## Sets up the file information of `c` from `frm`. Only needed when there's
  ## debug information.
  c.m.fileInfos.newSeq(frm.files.len)
  for i, f in frm.files.pairs:
    c.m.fileInfos[i].fullPath = f.AbsoluteFile

func pack*(dst: var PackedEnv, config: ConfigRef, c: sink VmEnv) =
  ## Stores all relevant data provided by `c` into `dst`. Previously stored
  ## data (except `nodes`, `numbers`, and `strings`) is thrown away. The only
  ## parts of `dst` not touched by `storeEnv` are: `cconsts`, `globals`, and
  ## `entryPoint`. These have to be filled in separately.

  dst.consts = c.constants
  dst.procs = c.procs
  dst.code = c.code
  dst.types = c.types

  mapList(dst.debug, c.debug, d):
    dst.infos.getOrIncl(d).uint32

  dst.ehTable = c.ehTable
  dst.ehCode = c.ehCode

  mapList(dst.files, config.m.fileInfos, fi):
    fi.fullPath.string

proc storePrim(f: var RodFile, p: IdentPattern) =
  storePrim(f, p.string)

proc loadPrim(f: var RodFile, p: var IdentPattern) =
  loadPrim(f, p.string)

proc writeToFile*(p: PackedEnv, file: AbsoluteFile): RodFileError =
  var f = rodfiles.create(file.string)
  f.storeHeader()

  # All changes here need to be reflected in `readFromFile`

  # The order in which the sections are stored doesn't match the data's
  # dependencies, but the rodfile format writer/parser dictates it this way.
  # Sorting the data into different sections is only done for stylistic
  # reasons, it has no semantic meaning.

  f.storeSection stringsSection
  f.store p.strings

  f.storeSection numbersSection
  f.store p.numbers

  f.storeSection topLevelSection
  f.storeSeq p.nodes
  f.storeSeq p.data
  f.storeSeq p.globals
  f.storeSeq p.consts

  f.storeSection bodiesSection
  f.storePrim p.entryPoint
  f.storeSeq p.code
  f.storeSeq p.debug
  f.storeSeq p.ehTable
  f.storeSeq p.ehCode

  f.storeSection symsSection
  f.store    p.infos
  f.storeSeq p.files
  f.storeSeq p.dbgSyms
  # f.storeSeq p.procs # TODO: remove sym from ProcEntry
  f.storeSeq p.callbacks

  f.storeSection typesSection
  f.storePrim p.types

  f.close()

  result = f.err

proc readFromFile*(p: var PackedEnv, file: AbsoluteFile): RodFileError =
  var f = rodfiles.open(file.string)
  f.loadHeader()

  f.loadSection stringsSection
  f.load p.strings

  f.loadSection numbersSection
  f.load p.numbers

  f.loadSection topLevelSection
  f.loadSeq p.nodes
  f.loadSeq p.data
  f.loadSeq p.globals
  f.loadSeq p.consts

  f.loadSection bodiesSection
  f.loadPrim p.entryPoint
  f.loadSeq p.code
  f.loadSeq p.debug
  f.loadSeq p.ehTable
  f.loadSeq p.ehCode

  f.loadSection symsSection
  f.load p.infos
  f.loadSeq p.files
  f.loadSeq p.dbgSyms
  # f.loadSeq p.procs # TODO: remove sym from ProcEntry
  f.loadSeq p.callbacks

  f.loadSection typesSection
  f.loadPrim p.types

  f.close()

  result = f.err
