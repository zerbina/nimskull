
{.experimental: "views".}

proc mutable_view() =
  var x = 0
  var mut: lent int = x
  doAssert mut == 0
  mut = 1
  doAssert mut == 1
  doAssert x == 1

mutable_view()

proc immutable_view() =
  var x = 0
  let mut: lent int = x
  doAssert mut == 0

immutable_view()

proc composite_view_object() =
  type Object = object
    other: int
    a: lent int

  let y = 1
  var x = Object(a: y)
  x.other = 1
  doAssert x.a == 1

composite_view_object()

proc composite_view_object_mutable() =
  type Object = object
    other: int
    a: var int

  var y = 1
  var x = Object(a: y)
  x.other = 5
  x.a = 2
  doAssert x.a == 2
  doAssert y == 2

composite_view_object_mutable()

proc composite_view_object_openArray() =
  type Object = object
    a: openArray[int]

  var y = @[1]
  var x = Object(a: y)
  doAssert x.a[0] == 1
  doAssert y[0] == 1

composite_view_object_openArray()

proc composite_view_object_openArray_mutable() =
  type Object = object
    a: var openArray[int]

  var y = @[1]
  var x = Object(a: y)
  doAssert x.a[0] == 1
  x.a[0] = 2
  doAssert x.a[0] == 2
  doAssert y[0] == 2

composite_view_object_openArray_mutable()
