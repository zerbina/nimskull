
{.experimental: "views".}

proc error() =
  proc a(a: var seq[int], b: var seq[int]) = discard

  var s = @[1]
  a(s, s) # error; mutable borrows of the same location

proc error_2() =
  type Container = object
    children: seq[Container]

  proc p(a, b: var Container) = discard

  var c = Container(children: @[Container()])
  p(c, c.children[0]) # error

proc error_3() =
  type Cont = object
    children: seq[ref Cont]

  proc inner(a: var Cont, b: ref Cont) = discard

  var x = Cont()
  x.children.add (ref Cont)()
  inner(x, x.children[0]) # not safe, because `b` is a 'lent' parameter
  # if parameter 'a' were a ref, the same issue exists, but - for ergonomic
  # reasons - no error is reported there

proc error_4() =
  type Cont = object
    children: seq[ref Cont]

  proc inner(a: var Cont, b: var Cont) =
    discard

  let p = (ref Cont)()
  var x = Cont(children: @[p])
  inner(x, p[]) # p[] could be modified by `x` (and through itself)

proc indirect_error() =
  type SomeObj = object
    x: ptr seq[int]

  proc p(x: var seq[int], y: SomeObj) =
    discard

  var x: ref seq[int]
  p(x[], SomeObj()) # error; there's a pointer to `seq[int]` in SomeObj
  # the actual arguments are ignored by the analysis, only the parameter types
  # count

proc indirect_error_2() =
  type SomeRef = ref object
    x: ptr seq[int]

  proc p(x: var seq[int], y: SomeRef) = discard

  var x: ref seq[int]
  p(x[], nil) # error; same reason as above

proc self_alias_error() =
  type Obj = object
    self: ref Obj

  proc inner(x: var Obj) = discard

  var x: ref Obj
  inner(x[]) # error; x could hold a ref to itself

var global = 0

proc side_effect_error() =
  proc p(x: var seq[int]) =
    global = 1

  # if arc|orc are enabled, seq[int] is a 'lent' parameter
  proc p2(x: seq[int]) =
    global = 1

  var r: ref seq[int]

  # p and p2 could read/write through a ref/ptr, for all we know
  p2(r[])
  p(r[])

  var pt: ptr seq[int]
  p2(pt[])
  p(pt[])

proc address_to_local() =
  proc p(x: seq[int]) =
    global = 1

  let x = @[1]
  p(x) # not an error; a let cannot (legally) be modified through a pointer
  var y = @[1]
  p(y) # works, but should it? some global could hold a pointer to `y`

proc local_borrow() =
  proc p1(x: seq[int], y: ptr seq[int]) =
    discard

  let a = @[1]
  p1(a, nil) # always safe; a let cannot legally be modified through a pointer
  var b = @[1]
  p1(b, nil) # error; the var could be modified

  proc p2(x: seq[int], y: ref seq[int]) = discard
  # always safe; a ref can only point to a heap location
  p2(a, nil)
  p2(b, nil)
