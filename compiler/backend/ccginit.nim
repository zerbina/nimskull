## Code specialization for the initilization logic previously performed by the
## RTTI-based ``objectInit`` procedure.
##
## Included from ``ccgtypes.nim``


proc genObjectInitHeader(p: BProc, section: TCProcSection, t: PType, r: Rope,
                         info: TLineInfo)

proc specializeInitObject(p: BProc, accessor: Rope, typ: PType,
                          info: TLineInfo)

proc specializeInitObjectL(p: BProc, accessor: Rope, loc: TLoc) =
  ## Generates type field (if there are any) initialization code for the given
  ## `loc`. `accessor` is the path to `loc`, excluding loc itself
  specializeInitObject(p, "$1.$2" % [accessor, loc.r], loc.t, loc.lode.info)

proc specializeInitObjectN(p: BProc, accessor: Rope, n: PNode, typ: PType) =
  ## Generates type field initialization code for the record node

  # XXX: this proc shares alot of code with `specializeResetN` (it's based on
  #      a copy of it, after all)
  if n == nil: return
  case n.kind
  of nkRecList:
    for i in 0..<n.len:
      specializeInitObjectN(p, accessor, n[i], typ)
  of nkRecCase:
    p.config.internalAssert(n[0].kind == nkSym, n.info,
                            "specializeInitObjectN")
    let disc = n[0].sym
    if disc.loc.r == nil: fillObjectFields(p.module, typ)
    p.config.internalAssert(disc.loc.t != nil, n.info,
                            "specializeInitObjectN()")
    lineF(p, cpsStmts, "switch ($1.$2) {$n", [accessor, disc.loc.r])
    for i in 1..<n.len:
      let branch = n[i]
      assert branch.kind in {nkOfBranch, nkElse}
      if branch.kind == nkOfBranch:
        genCaseRange(p, branch)
      else:
        lineF(p, cpsStmts, "default:$n", [])
      specializeInitObjectN(p, accessor, lastSon(branch), typ)
      lineF(p, cpsStmts, "break;$n", [])
    lineF(p, cpsStmts, "} $n", [])
  of nkSym:
    let field = n.sym
    if field.typ.kind == tyVoid: return
    if field.loc.r == nil: fillObjectFields(p.module, typ)
    p.config.internalAssert(field.loc.t != nil, n.info,
                            "specializeInitObjectN()")
    specializeInitObjectL(p, accessor, field.loc)
  else: internalError(p.config, n.info, "specializeInitObjectN()")

proc specializeInitObject(p: BProc, accessor: Rope, typ: PType,
                          info: TLineInfo) =
  ## Generates type field (if there are any) initialization code for an
  ## variable of `typ` at `accessor`. Specialiaztion for the run-time
  ## `objectInit` function (that's also only available for the old runtime)
  if typ == nil:
    return

  let typ = typ.skipTypes(abstractInst)

  # XXX: this function trades compililation time for run-time efficiency by
  #      potentially performing lots of redundant walks over the same types,
  #      in order to not generate code for records that don't need it. The
  #      better solution would be to run type field analysis only once for
  #      each record type and then cache the result. `cgen` lacks a general
  #      mechanism for caching type related info.
  #      A further improvement would be to emit the code into a separate
  #      function and then just call that

  case typ.kind
  of tyArray:
    # To not generate an empty `for` loop, first check if the array contains
    # any type fields. This optimizes for the case where there are none,
    # making the case where type fields exist slower (compile time)
    if analyseObjectWithTypeField(typ) == frNone:
      return

    let arraySize = lengthOrd(p.config, typ[0])
    var i: TLoc
    getTemp(p, getSysType(p.module.g.graph, info, tyInt), i)
    linefmt(p, cpsStmts, "for ($1 = 0; $1 < $2; $1++) {$n",
            [i.r, arraySize])
    specializeInitObject(p, ropecg(p.module, "$1[$2]", [accessor, i.r]),
                         typ[1], info)
    lineF(p, cpsStmts, "}$n", [])
  of tyObject:
    proc pred(t: PType): bool = not isObjLackingTypeField(t)

    var
      t = typ
      a = accessor

    # walk the type hierarchy and generate object initialization code for
    # all bases that contain type fields
    while t != nil:
      t = t.skipTypes(skipPtrs)

      if t.n != nil and searchTypeNodeFor(t.n, pred):
        specializeInitObjectN(p, a, t.n, t)

      a = a.parentObj(p.module)
      t = t.base

    # type header:
    if pred(typ):
      genObjectInitHeader(p, cpsStmts, typ, accessor, info)

  of tyTuple:
    let typ = getUniqueType(typ)
    for i in 0..<typ.len:
      specializeInitObject(p, ropecg(p.module, "$1.Field$2", [accessor, i]),
                           typ[i], info)

  else:
    discard

proc requestObjectInit(m: BModule, origTyp: PType, info: TLineInfo) =
  ## Requests the creation of an ``objectInit`` specialization for the given
  ## `origType`. If the specialization was not yet created, it's first created
  ## and then registered with the RTTI object of `origTyp`
  case analyseObjectWithTypeField(origTyp)
  of frHeader, frEmbedded:
    let sig = hashType(origTyp)
    if not m.g.objInitProcMarker.containsOrIncl(sig):
      let
        tinfo = genTypeInfoV1(m, origTyp, info)
        owner = origTyp.itemId.module
        module = m.g.modules[owner]

      m.config.internalAssert(moduleOpenForCodegen(m.g.graph, FileIndex owner))

      let
        name = "ObjectInit_" & getTypeName(m, origTyp, sig)
        header = "static N_NIMCALL(void, $1)(void* p)" % [name]
        p = newProc(nil, module)
        typ = origTyp.skipTypes(abstractInstOwned)
        tdesc = getTypeDesc(m, typ)

      # TODO: make this work for array types

      lineF(p, cpsLocals, "$1* a;$n", [tdesc])
      lineF(p, cpsInit, "a = ($1*) p;$n", [tdesc])

      specializeInitObject(p, ~"(*a)", typ, info)

      let generatedProc = "$1 {$n$2$3$4}$n" %
            [header, p.s(cpsLocals), p.s(cpsInit), p.s(cpsStmts)]

      # register the procedure to the owning module
      module.s[cfsProcHeaders].addf("$1;$n", [header])
      module.s[cfsProcs].add(generatedProc)

      # register the procedure with the type-info
      module.s[cfsTypeInit3].addf("$1->init = $2;$n", [tinfo, name])

  of frNone:
    discard
