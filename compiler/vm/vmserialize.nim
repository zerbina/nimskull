## Implements routines for initializing VM memory locations directly from
## expressions.

import
  compiler/ast/[
    ast_query,
    ast_types,
    types
  ],
  compiler/front/[
    options
  ],
  compiler/mir/[
    mirenv,
    mirtrees
  ],
  compiler/vm/[
    vmaux,
    vmdef,
    vmobjects,
    vmalloc,
    # vmmemory,
    vmtypegen,
    vmtypes
  ],
  compiler/utils/[
    bitsets,
    containers,
    idioms,
    int128
  ]

proc getInt(env: MirEnv, n: MirNode): Int128 =
  case n.kind
  of mnkIntLit:  env.getInt(n.number).toInt128
  of mnkUIntLit: env.getUInt(n.number).toInt128
  else:          unreachable(n.kind)

template mslice(dest: HostPointer, lo, hi: int): var openArray[byte] =
  var d = dest
  toOpenArray(d, lo, hi)

proc lookupField(env: VmTypeEnv, orig: PType, typ: VmTypeId, pos: int32): Field =
  ## Maps
  assert env.types[typ].kind == akRecord
  var local = env.types[typ].a
  if orig[0] != nil:
    result = lookupField(env, orig[0], env.fields[env.types[typ].a].typ, pos)
    if result.typ != VoidType:
      return
    inc local

  proc traverse(env: VmTypeEnv, n: PNode, typ: VmTypeId, pos: int32, local: var uint32): Field {.nimcall.} =
    case n.kind
    of nkSym:
      if n.sym.position == pos:
        return env.fields[local]
      inc local
    of nkRecList:
      for it in n.items:
        result = traverse(env, it, typ, pos, local)
        if result.typ != VoidType:
          return

    of nkRecCase:
      let inner = env.fields[local].typ
      if n[0].sym.position == pos:
        return env.fields[env.types[inner].a + 0]

      var lo = env.types[inner].a + 2
      for i in 1..<n.len:
        result = traverse(env, n[^1], typ, pos, lo)
        if result.typ != VoidType:
          return
      inc local
    else:
      unreachable()

  result = traverse(env, orig.n, typ, pos, local)

proc fieldFor(x: VmTypeEnv, id: VmTypeId, f: uint32): Field =
  x.fields[x.types[id].a + f]

proc initFromExpr(dest: HostPointer, typ: VmTypeId,
                  tree: MirTree, n: var int, env: MirEnv,
                  config: ConfigRef, c: var VmEnv) =
  ## Loads the value represented by `tree` at `n` into `dest`. On exit, `n`
  ## points to the next sub-tree.
  # TODO: the host memory region could grow, meaning that initFromExpr must
  #       take a virtual address instead
  template recurse(dest: HostPointer, typ: VmTypeId) =
    initFromExpr(dest, typ, tree, n, env, config, c)

  template next(): lent MirNode =
    let i = n
    inc n
    tree[i]

  template arg(body: untyped) =
    inc n # skip the ``mnkArg`` node
    body

  template iterTree(name, body: untyped) =
    let len = next().len
    for name in 0..<len:
      body

  # echo "type: ", c.types[typ]

  case c.types[typ].kind
  of akInt:
    dest.store(env.getUInt(next().number), c.types[typ].size)
  of akFloat:
    if c.types[typ].size == 4:
      dest.store(float32(env.getFloat(next().number)))
    else:
      dest.store(float64(env.getFloat(next().number)))
  of akString:
    c.allocator.newString(dest, env[next().strVal])
  of akSeq:
    # allocate the sequence first:
    c.allocator.newSeq(c.allocator.mapBack(dest), tree[n].len.int64, c.types[c.types[typ].elem].size)
    # then initialize the elements:
    let v = c.allocator.translate(dest.rd(VirtualAddr, 8) + 8)
    iterTree(j):
      arg recurse(v + (j * c.types[c.types[typ].elem].size), c.types[typ].elem)
  of akPtr:
    # nothing to do, only nil literals are allowed here
    discard next()
  of akRef:
    if tree[n].kind == mnkNilLit:
      discard next() # nothing to do for 'nil' literals
    else:
      # allocate a managed heap location and fill it:
      # let
      #   t = c.getOrCreate(env[tree[n].typ])
      #   slot = c.allocator.newRc(c.types[dest.typ].elem)
      # recurse(c.heap.unsafeDeref(slot))
      # deref(dest).refVal = slot
      missing("ref serialization")
  of akSet:
    proc adjusted(val, first: Int128): BiggestInt {.inline.} =
      # subtract the first element's value to make all values zero-based
      toInt(val - first)

    let first =
      if tree[n].len > 0: firstOrd(config, env[tree[n].typ])
      else:               Zero
    # XXX: ^^ ``set[empty]``-typed literals reach here, but they shouldn't. The
    #      len guard works around the issue
    let size = c.types[typ].size.int
    iterTree(j):
      let node = next()
      if node.kind == mnkRange:
        let
          a = adjusted(env.getInt(next()), first)
          b = adjusted(env.getInt(next()), first)
        bitSetInclRange(mslice(dest, 0, size), a .. b)
      else:
        bitSetIncl(mslice(dest, 0, size), adjusted(env.getInt(node), first))
  of akForeign:
    dest.store(c.allocator.register(env[next().ast]))
  of akProc:
    dest.store(toFuncPtr FunctionIndex(next().prc))
  of akRecord:
    # the source can either be an object or tuple constructor
    case tree[n].kind
    of mnkNilLit:
      # special case: nil closure literal
      # only skip the node, don't initialize anything
      discard next()
    of mnkTupleConstr, mnkClosureConstr:
      iterTree(j):
        let f = c.types.fieldFor(typ, j)
        arg recurse(dest + f.off, f.typ)
    of mnkObjConstr, mnkRefConstr:
      let orig = env[tree[n].typ].skipTypes(abstractPtrs) ## the object's type
      iterTree(i):
        inc n # skip the binding node
        let sym = lookupInType(orig, next().field)
        # TODO: handle inheritance and case objects properly
        if sfDiscriminant in sym.flags:
          echo "field: ", sym
        arg recurse(dest + sym.offset.uint, c.types.lookupField(orig, typ, sym.position.int32).typ)
    else:
      unreachable(tree[n].kind)
  of akArray:
    let (_, typ) = c.types.unpackArray(typ)
    iterTree(i):
      arg recurse(dest + (c.types[typ].size * i), typ)
  of akUnion, akVoid, akFlexArray:
    unreachable("raw unions cannot reach here")

proc initFromExpr*(dest: HostPointer, typ: VmTypeId, tree: MirTree, env: MirEnv,
                   config: ConfigRef, c: var VmEnv) {.inline.} =
  ## Intializes the memory location `dest` with the value represented by the
  ## MIR contant expression `tree`. The location is expected to be in its
  ## zero'ed state.
  var i = 0
  initFromExpr(dest, typ, tree, i, env, config, c)
