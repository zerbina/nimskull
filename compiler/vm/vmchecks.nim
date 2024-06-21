## This module implements the handle validation logic.
##
## After making making sure that the handle references a valid cell (it's an
## error otherwise), the layout of cell is traversed in order to verify that
## there exists a valid location of the handle's type at the offset relative to
## the start of the cell.
##
## Special handling is required for variant objects, since whether a
## sub-location is valid depends on the run-time value of the respective
## disciminator(s) there.

import
  std/options,
  compiler/utils/[
    idioms
  ],
  compiler/vm/[
    vmdef,
    vmtypes,
    vmalloc,
    vmobjects
  ]

when defined(release):
  {.push checks: off.}

proc typecheck*(types: VmTypeEnv, typ: VmTypeId, p: HostPointer, offset: uint, expect: VmTypeId): bool =
  # same ID == same type
  if offset == 0 and expect == typ:
    false # valid
  elif types[typ].kind == akRecord:
    # TODO: improve
    for _, f in fields(types, typ):
      if f.off <= offset and f.off + types[f.typ].size > offset:
        return typecheck(types, f.typ, p + f.off, offset - f.off, expect)
    true # not part of the record
  elif types[typ].kind == akArray:
    let (count, elem) = types.unpackArray(typ)
    if count * types[elem].size > offset:
      let bias = (offset div types[elem].size) * types[elem].size
      typecheck(types, elem, p + bias, offset - bias, expect)
    else:
      true
  elif types[typ].kind == akUnion:
    # select the active branch based on the discriminator
    let sel = types.fields[types[typ].a].typ
    let x = p.readUInt(types[sel].size.int)
    let branch = selectBranch(x, types, typ)
    if branch >= 0:
      # select the active branch and continue
      typecheck(types, types.fieldAt(typ, 1 + branch), p, offset, expect)
    else:
      true # the discriminator value is corrupt
  else:
    true # location

proc getType*(types: VmTypeEnv, typ: VmTypeId, p: HostPointer, offset: uint, closest: var uint): Option[VmTypeId] =
  # XXX: for testing only
  if types[typ].kind == akRecord:
    echo "step: ", types[typ], " id: ", typ.int
    for _, f in fields(types, typ):
      if f.off <= offset and f.off + types[f.typ].size > offset:
        echo "step into: ", offset, " field: ", f.off
        return getType(types, f.typ, p + f.off, offset - f.off, closest)
    echo "no 1"
    none VmTypeId # not part of the record
  elif types[typ].kind == akArray:
    echo "step: ", types[typ]
    let (count, elem) = types.unpackArray(typ)
    if count * types[elem].size > offset:
      let bias = (offset div types[elem].size) * types[elem].size
      getType(types, elem, p + bias, offset - bias, closest)
    else:
      none VmTypeId
  else:
    closest = offset
    some typ # found a non-aggregate type
