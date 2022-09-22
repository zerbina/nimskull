## The type definitions for the old-style run-time-type-information

type
  TNimTypeFlag = enum
    ntfNoRefs = 0     # type contains no tyRef, tySequence, tyString

  TNimType {.compilerproc.} = object
    when defined(gcHooks):
      head*: pointer

    size*: int          ## the size in bytes
    align*: int         ## the alignment in bytes
    flags*: set[TNimTypeFlag]
    base*: ptr TNimType ## for ``object`` types, the base type (or nil if none)
                        ## for container types (``seq``, ``ref``, ``ptr``,
                        ## etc.), the element type
                        ## for all other types, nil

    finalizer*: pointer ## the finalizer for the type. Only used for
                        ##``ref object``
    init*: proc (p: pointer) {.nimcall, tags: [], raises: [].}
      ## initializes a location to it's default state. For example, it's used
      ## to initialize type-header fields embedded in objects. May be 'nil'
    destroy*: proc (p: pointer) {.nimcall, benign, tags: [], raises: [].}
      ## destroys a single location. Either a ``=destroy`` hook or the
      ## decrement-ref operator for ref-like types. May be 'nil'
    marker*: proc (p: pointer, op: int) {.nimcall, benign, tags: [], raises: [].}
      ## marker proc for the GC. Applies the given `op` to all GC-relevant
      ## locations that are part of the type.
      ## Must be set for all types passed to ``newObj``.
    deepcopy: proc (p: pointer): pointer {.nimcall, benign, tags: [], raises: [].}

    when defined(nimSeqsV2):
      typeInfoV2*: pointer
    when defined(nimTypeNames):
      name: cstring
      nextType: ptr TNimType # next item in the linked-list
      instances: int # count the number of instances
      sizes: int # sizes of all instances in bytes

when defined(gcHooks):
  type
    PNimType* = ptr TNimType
else:
  type
    PNimType = ptr TNimType

when defined(nimTypeNames):
  # Declare this variable only once in system.nim
  when declared(ThisIsSystem):
    var nimTypeRoot {.compilerproc.}: PNimType
      ## the head of the singly-linked-list storing all existing ``TNimType``s
  else:
    var nimTypeRoot {.importc.}: PNimType
