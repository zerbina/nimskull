
{.experimental: "views".}

proc illegal_type(): lent openArray[int] = # not allowed
  var x: var openArray[int] # not allowed
  type ViewA = object
    x: openArray[int]
  var y: lent ViewA # not allowed

proc cannot_modify_immutable_view() =
  var x = 0
  let mut: lent int = x
  mut = 1 # error

proc cannnot_mutably_borrow_from_immutable() =
  let x = 0
  var mut: lent int = x # error
  mut = 1

proc valid1() =
  type Object = object
    v: lent int

  var y = 0
  var x = Object(v: y)
  if true:
    var o = 0
    x = Object(v: o)
    discard x.v

  y = 0

proc illegal1() =
  type Object = object
    v: lent int

  var y = 0
  var x = Object(v: y)
  if true:
    var o = 0
    x = Object(v: o)

  y = 0
  discard x.v

proc legal() =
  var arr = [0, 1]
  let b: lent int = arr[0]
  arr[1] = 2
  discard b # paths are statically disjoint -> valid

proc illegal_5(i: int) =
  var arr = [0, 1]
  let b: lent int = arr[0]
  arr[i] = 1
  discard b # paths are not statically disjoint -> valid

proc legal_1() =
  var s = @[1]
  let o: openArray[int] = s
  discard s[0]
  discard o[0]
  discard s[0]

proc illegal_4() =
  var s = @[1]
  let o: openArray[int] = s
  s[0] = 1
  discard o[0]

proc illegal_2() =
  var s = @[1]
  var o: openArray[int] = s
  # these are fine:
  discard s[0]
  discard o[0]
  # this is not:
  o[0] = 0

proc illegal_3() =
  type Obj = object
    a: lent int
    b: int

  # should this really be illegal? Strictly speaking the borrow of `y` start
  # before the `y = 1` assignment

  var y = 0
  var x = Obj(a: y,
              b: (y = 1; 1)) # <- the problematic mutation
  discard x.a

var global = 0

proc p(x: var int) = # has side effects
  global = 1

proc illegal_global_1() =
  p(global)

proc illegal_global_2() =
  var x: lent int = global
  var y = 0
  p(y) # might mutate or use `global` (because it has side-effects)
  discard x

proc multi_borrows() =
  var x = 0
  let y: lent int = x # immutable borrow
  let z: lent int = x # immutably borrow again
  discard z # use; this is fine
  discard y

  var mut: lent int = x # mutable borrow; this is fine too
  # but this is not (because a mutable borrow was created):
  discard y

proc multi_composite_borrows() =
  type Object = object
    a: lent int
    b: lent int

  var y = 1
  let x = Object(a: y, b: y)
  # not an error
  echo x.a
  echo x.b

proc multi_composite_borrows_mutable() =
  type Object = object
    a: var int
    b: var int

  var y = 1
  var x = Object(a: y, b: y) # not an error itself
  discard x.a # still not an error (unsure)
  discard x.b # still not an error
  x.a = 2 # now it is

proc array_composite_view() =
  var y = 0
  # doesn't work yet
  var x: array[2, var int] = [y, y]
  discard

type View = object
  x: lent int

proc composite_result(x: int): View =
  var local = 0
  result = View(x: local) # error

proc composite_result_2(x: var int): View =
  result = View(x: x) # no error

proc composite_result_2(x: var View): View =
  result = x # error
