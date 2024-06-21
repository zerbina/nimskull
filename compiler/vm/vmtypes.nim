## This module contains various functions for querying information about
## `VmType`s and working with them in general.

import
  compiler/utils/[
    idioms,
    containers
  ]

type
  VmTypeId* = #[distinct]# uint32
    ## The unique ID of a `VmType`. Implementation-wise, it's an index into
    ## `TypeInfoCache.types`

  AtomKind* = enum
    akVoid
    akInt, akFloat
    akPtr, akRef, akProc
    akSet

    akString, akSeq

    akForeign

    akRecord, akUnion
    akArray
    akFlexArray ## flexible array

  VmTypeFlag* = enum
    vtfDataOnly

  VmType* = object
    ## Run-time type information (=RTTI). Flat in-memory representation so
    ## that it's easily serializable.
    kind*: AtomKind
    flags*: set[VmTypeFlag]
    align*: uint8
    size*: uint32 # 4GB per statically-sized location should be plenty enough
    a*: uint32 ## meaning depends on the kind
    b*: uint32 ## meaning depends on the kind

  Field* = object
    off*: uint32
    typ*: VmTypeId

  Selector* = object
    isRange*: bool
    branch*: uint32
    val*: uint64

  VmTypeEnv* = object
    ## Flat and data-oriented for the purpose of being easy to serialize and
    ## fast to operate on. Arrays-of-structs based storage.
    types*: Store[VmTypeId, VmType]
    fields*: seq[Field]
      ## meaning depends on the viewer, but generally stores record field
      ## information
    selectors*: seq[Selector]
      ## discriminator description table. Provides the information for mapping
      ## discriminator values to a branch index

const VoidType* = VmTypeId(0)

type VmTypeRel* = enum
  vtrUnrelated
  vtrSame
  vtrSub
  vtrSuper

template `[]`*(e: VmTypeEnv, id: VmTypeId): VmType =
  e.types[id]

iterator fields*(e: VmTypeEnv, id: VmTypeId): (int, Field) =
  var i = e.types[id].a
  let fin = e.types[id].b
  while i < fin:
    yield (int(i - e.types[id].a), e.fields[i])
    inc i

iterator parameters*(e: VmTypeEnv, id: VmTypeId): (int, VmTypeId) =
  var i = e.types[id].a + 1
  let fin = e.types[id].b
  while i < fin:
    yield (int(i - e.types[id].a), e.fields[i].typ)
    inc i

proc param*(e: VmTypeEnv, id: VmTypeId, i: Natural): VmTypeId =
  e.fields[e.types[id].a + 1 + uint32(i)].typ


proc returnType*(e: VmTypeEnv, id: VmTypeId): VmTypeId =
  e.fields[e.types[id].a].typ

proc fieldAt*(e: VmTypeEnv, id: VmTypeId, i: int): VmTypeId =
  e.fields[e.types[id].a + uint32(i)].typ

proc branch*(e: VmTypeEnv, id: VmTypeId, i: Natural): VmTypeId =
  e.fields[e.types[id].a + 2 + uint32(i)].typ

proc unpackArray*(e: VmTypeEnv, id: VmTypeId): tuple[len: uint32, elem: VmTypeId] =
  let f = e.fields[e.types[id].a]
  result = (f.off, f.typ)

func len*(t: VmType): int {.inline.} =
  int(t.b - t.a)

template elem*(typ: VmType): VmTypeId =
  typ.a.VmTypeId

func alignedSize*(t: VmType): uint {.inline.} =
  let a = 1'u shl t.align
  (t.size + (a - 1)) and not (a - 1)
