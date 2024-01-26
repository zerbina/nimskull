
type
  UnaryOpKind = enum
    Neg
  BinaryOpKind = enum
    Add, Sub

  Node = case
    of Asgn:
      left, right: ref Node
    of Sym:
      name: string
    of IntLit:
      value: int
    of FloatLit:
      value: float
    of CheckedUnaryOp, UnaryOp:
      kind: UnaryOpKind
      operand: ref Node
    of BinaryOp:
      kind: BinaryOpKind
      a, b: ref Node
    of StmtList:
      nodes: seq[Node]

proc `$`(x: Node): string =
  case x
  of Asgn:
    "(Asgn " & ($x.left[]) & " " & ($x.right[]) & ")"
  of Sym:
    "(Sym \"" & x.name & "\")"
  of IntLit:
    "(IntLit " & $x.value & ")"
  of FloatLit:
    "(FloatLit " & $x.value & ")"
  of CheckedUnaryOp, UnaryOp, BinaryOp, StmtList:
    "<missing>"

proc `$`(x: ref Node): string =
  if x.isNil:
    "<nil>"
  else:
    $(x[])

proc evalAsgn(n: Asgn) =
  echo n.left

proc eval(n: Node) =
  case n
  of Asgn as x:
    evalAsgn(x)
  of Sym:
    discard
  of IntLit:
    echo n.value
  of FloatLit:
    echo n.value
  of CheckedUnaryOp, UnaryOp, BinaryOp:
    discard
  of StmtList as n:
    for it in n.nodes:
      eval(it)

# implicit conversion:
eval(IntLit(value: 2))
# explicit conversion:
eval(Node(FloatLit(value: 1)))

proc testNotAllCovered(n: Node) =
  # not all labels need to be covered. If there's no match at run-time, an
  # exception is raised
  case n
  of Asgn:
    echo n

testNotAllCovered(Asgn(left: (ref Node)(Sym(name: "")),
                       right: (ref Node)(IntLit(value: 1))))
doAssertRaises ReraiseDefect:
  # will fail at run-time:
  testNotAllCovered(IntLit(value: 2))

proc testMultiLabelBinding(n: Node) =
  proc test(x: UnaryOp) =
    discard

  case n
  of CheckedUnaryOp, UnaryOp as n:
    doAssert n.kind == Neg
    # `n` is of the anonymous common ancestor type:
    doAssert $typeof(n) == ":anonymous"
    doAssert not compiles(test(n))

testMultiLabelBinding(UnaryOp(kind: Neg, operand: nil))

#[
# XXX: doesn't work yet, needs a parser extension
proc testGeneric[T: case](n: T) =
  discard
proc testGeneric[T: object](n: T) =
  {.error: "shouldn't match".}

testGeneric(Node(BinaryOp(kind: Add)))
]#