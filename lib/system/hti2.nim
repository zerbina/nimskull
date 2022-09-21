
type
  TNimType {.compilerproc.} = object
    when defined(gcHooks):
      head*: pointer
    size*: int
    align*: int
    base*: ptr TNimType
    finalizer*: pointer # the finalizer for the type
    init*: proc (p: pointer) {.nimcall, tags: [], raises: [].}
    destroy*: proc (p: pointer) {.nimcall, benign, tags: [], raises: [].}
    marker*: proc (p: pointer, op: int) {.nimcall, benign, tags: [], raises: [].} # marker proc for GC
    deepcopy: proc (p: pointer): pointer {.nimcall, benign, tags: [], raises: [].}
    when defined(nimSeqsV2):
      typeInfoV2*: pointer
    when defined(nimTypeNames):
      name: cstring
      nextType: ptr TNimType
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
  else:
    var nimTypeRoot {.importc.}: PNimType
