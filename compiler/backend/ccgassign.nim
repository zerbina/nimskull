## Implements the lifting of assignment logic into 'copy' procedures. This is
## only necessary for `seq` types and for compound types that contain GC'ed
## memory or type-headers.
##
## Replaces the RTTI-based ``genericAssign`` and ``genericSeqAssign``.
##
## Included from ``cgen.nim``

type
  TAsgnClosure = object
    p: BProc
    dst, src, shallow: Rope

proc genAsgnProc(c: TAsgnClosure, accessor: Rope, typ: PType)
proc genAsgnProc(c: TAsgnClosure, accessor: Rope, n: PNode;
                     typ: PType)
proc genAsgnProc(m: BModule, origTyp: PType; sig: SigHash): Rope
proc genAsgnProc(m: BModule, t: PType): Rope

proc genAsgn(c: TAsgnClosure, accessor: Rope, typ: PType) =
  var dst, src: TLoc
  let n = newNodeIT(nkEmpty, unknownLineInfo, typ)
  fillLoc(dst, locField, n, ropecg(c.p.module, "($1$2)", [c.dst, accessor]), OnUnknown)
  fillLoc(src, locField, n, ropecg(c.p.module, "($1$2)", [c.src, accessor]), OnUnknown)
  genAssignment(c.p, dst, src, {needToCopy})


proc specializeResetB(p: BProc, accessor: Rope, n: PNode;
                      typ: PType, disc: PSym, branchIdx: int) =

  lineF(p, cpsStmts, "switch ($1.$2) {$n", [accessor, disc.loc.r])
  for i in 1..<n.len:
    let branch = n[i]
    assert branch.kind in {nkOfBranch, nkElse}
    if branch.kind == nkOfBranch:
      genCaseRange(p, branch)
    else:
      lineF(p, cpsStmts, "default:$n", [])

    # reset all branches not matching the one we're searching for
    if branchIdx != i:
      specializeResetN(p, accessor, lastSon(branch), typ)

    lineF(p, cpsStmts, "break;$n", [])

  lineF(p, cpsStmts, "} $n", [])

proc genBranchSelect(c: TAsgnClosure, accessor: Rope, n: PNode, typ: PType) =
  c.p.config.internalAssert(n[0].kind == nkSym, n.info, "genAsgnProc")
  let
    p = c.p
    disc = n[0].sym

  if disc.loc.r == nil:
    fillObjectFields(p.module, typ)

  p.config.internalAssert(disc.loc.t != nil, n.info, "genAsgnProc()")

  var tmp: TLoc
  getTemp(p, getSysType(c.p.module.g.graph, unknownLineInfo, tyInt), tmp)

  lineF(p, cpsStmts, "switch ($1$2.$3) {$n", [c.src, accessor, disc.loc.r])
  for i in 1..<n.len:
    let branch = n[i]
    assert branch.kind in {nkOfBranch, nkElse}
    if branch.kind == nkOfBranch:
      genCaseRange(c.p, branch)
    else:
      lineF(p, cpsStmts, "default:$n", [])

    specializeResetB(p, ropecg(p.module, "$1$2", [c.dst, accessor]), n, typ, disc, i)
    # copy the discriminator
    genAsgn(c, ropecg(p.module, "$1.$2", [accessor, disc.loc.r]), disc.typ)

    genAsgnProc(c, accessor, lastSon(branch), typ)

    lineF(p, cpsStmts, "break;$n", [])
  lineF(p, cpsStmts, "}$n", [])

proc genAsgnProc(c: TAsgnClosure, accessor: Rope, n: PNode;
                     typ: PType) =
  if n == nil: return
  case n.kind
  of nkRecList:
    for i in 0..<n.len:
      genAsgnProc(c, accessor, n[i], typ)

  of nkRecCase:
    genBranchSelect(c, accessor, n, typ)
  of nkSym:
    let field = n.sym
    if field.typ.kind == tyVoid: return
    if field.loc.r == nil: fillObjectFields(c.p.module, typ)
    c.p.config.internalAssert(field.loc.t != nil, n.info, "genAsgnProc()")
    genAsgnProc(c, "$1.$2" % [accessor, field.loc.r], field.loc.t)
  else:
    internalError(c.p.config, n.info, "genAsgnProc()")

proc genAsgnProc(c: TAsgnClosure, accessor: Rope, typ: PType) =
  if typ == nil: return

  var p = c.p
  case typ.kind
  of tyGenericInst, tyGenericBody, tyTypeDesc, tyAlias, tyDistinct, tyInferred,
     tySink, tyOwned:
    genAsgnProc(c, accessor, lastSon(typ))
  of tyArray:
    let arraySize = lengthOrd(c.p.config, typ[0])
    if tfHasGCedMem in typ.flags:
      # if the array contains GC'ed memory, we have to generate the copy logic
      # manually - calling ``genAssignment`` (via ``genAsgn``) would lead to
      # infinite recursion in this case
      var i: TLoc
      getTemp(p, getSysType(c.p.module.g.graph, unknownLineInfo, tyInt), i)
      let oldCode = p.s(cpsStmts)
      linefmt(p, cpsStmts, "for ($1 = 0; $1 < $2; $1++) {$n",
              [i.r, arraySize])
      let oldLen = p.s(cpsStmts).len
      genAsgn(c, ropecg(c.p.module, "$1[$2]", [accessor, i.r]), typ[1])

      lineF(p, cpsStmts, "}$n", [])
    else:
      genAsgn(c, accessor, typ)

  of tyTuple:
    let typ = getUniqueType(typ)
    for i in 0..<typ.len:
      genAsgnProc(c, ropecg(c.p.module, "$1.Field$2", [accessor, i]), typ[i])

  of tyObject:
    if tfHasGCedMem in typ.flags:
      let prc = genAsgnProc(c.p.module, typ)
      linefmt(p, cpsStmts, "$5((void*)&($2$1), (void*)&($3$1), $4);$n", [accessor, c.dst, c.src, c.shallow, prc])
    else:
      genAsgn(c, accessor, typ)

  of tySequence, tyString:
    if optSeqDestructors in c.p.config.globalOptions:
      genAsgn(c, accessor, typ)

    else:
      let prc = genAsgnProc(c.p.module, typ)
      linefmt(p, cpsStmts, "$5((void*)&($2$1), (void*)&($3$1), $4);$n", [accessor, c.dst, c.src, c.shallow, prc])

  of tyRef, tyProc:
    genAsgn(c, accessor, typ)

  else:
    genAsgn(c, accessor, typ)

proc genAsgnProc(m: BModule, origTyp: PType; sig: SigHash): Rope =
  result = m.asgnProcMarker.getOrDefault(sig)
  if result != nil:
    # procedure already declared in this module
    return

  let item = m.g.asgnProcMarker.getOrDefault(sig)
  if item.str != nil:
    # procedure defined in another module, but not yet declared in the
    # current one

    # create a prototype for the procedure
    let header = "extern N_NIMCALL(void, $1)(void* dst, void* src, NIM_BOOL shallow)" % [item.str]
    m.s[cfsProcHeaders].addf("$1;\n", [header])

    # remember that we created a prototype
    m.asgnProcMarker[sig] = item.str
    return item.str

  result = "Assign_" & getTypeName(m, origTyp, sig)

  m.asgnProcMarker[sig] = result

  let
    typ = origTyp.skipTypes(abstractInstOwned)
    header = "N_LIB_PRIVATE N_NIMCALL(void, $1)(void* dst, void* src, NIM_BOOL shallow)" % [result]
    t = getTypeDesc(m, typ)

  m.s[cfsProcHeaders].addf("$1;\n", [header])

  let owner = typ.itemId.module
  if owner != m.module.position and moduleOpenForCodegen(m.g.graph, FileIndex owner):
    return genAsgnProc(m.g.modules[owner], origTyp, sig)

  m.g.asgnProcMarker[sig] = (str: result, owner: owner)

  var c: TAsgnClosure
  var p = newProc(nil, m)

  lineF(p, cpsLocals, "$1* a;$n", [t])
  lineF(p, cpsLocals, "$1* b;$n", [t])
  lineF(p, cpsInit, "a = ($1*)dst;$n", [t])
  lineF(p, cpsInit, "b = ($1*)src;$n", [t])

  c.p = p
  c.dst = ~"a"
  c.src = ~"b"
  c.shallow = ~"shallow"

  assert tfHasAsgn notin typ.flags

  case typ.kind
  of tySequence:
    var prc = genAsgnProc(c.p.module, typ[0])
    if prc == nil:
      prc = ~"NIM_NIL"

    lineCg(p, cpsStmts, "#copySeq(a, (#TGenericSeq*)*b, $1, $2, shallow);$n", [genTypeInfoV1(m, typ, unknownLineInfo), prc])

  of tyObject:
    c.dst = ~"(*a)"
    c.src = ~"(*b)"

    if typ[0] != nil:
      # generate an assignment through ``genAssignment``. If the base type
      # also needs a dedicated assignment procedure, ``genAsgnProc`` is called
      # again
      genAsgn(c, parentObj(~"", c.p.module), typ[0].skipTypes(skipPtrs))
    elif not isObjLackingTypeField(typ):
      # copy the type header
      lineCg(p, cpsStmts, "a->m_type = b->m_type;$n", [])

    if typ.n != nil:
      genAsgnProc(c, ~"", typ.n, typ)

  of tyTuple, tyArray:
    c.dst = ~"(*a)"
    c.src = ~"(*b)"
    genAsgnProc(c, ~"", typ)
  else:
    echo "missing: ", typ.kind

  let generatedProc = "$1 {$n$2$3$4}\n" %
        [header, p.s(cpsLocals), p.s(cpsInit), p.s(cpsStmts)]

  m.s[cfsProcs].add(generatedProc)

proc genAsgnProc(m: BModule, t: PType): Rope =
  let st = t.skipTypes(abstractVarRange)

  case st.kind
  of tyString:
    cgsym(m, "assignString")
  of tyRef:
    cgsym(m, "genericRefAssign")
  of tySequence:
    genAsgnProc(m, t, hashType(t))
  else:
    if tfHasGCedMem in t.flags or tfHasGCedMem in st.flags:
      genAsgnProc(m, t, hashType(t))
    else:
      # type doesn't need a code-specialized assignment procedure
      nil