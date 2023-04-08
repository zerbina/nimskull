discard """
  targets: "c js vm"
  description: '''
    Tests for the symbol binding behaviour of subscript-like operators in
    templates and generic routines
  '''
"""

type
  Obj = object
    val: int
  Other = object
    val: int

template generateOperators(T, index: untyped) {.dirty.} =
  ## Generates the subscript operator overloads. The idea is to invoke the
  ## template multiple times with different `index` names in order to create
  ## overloads that are ambiguous during overloading, but not at the
  ## definition site (because of the different parameter names)
  proc `[]`(x: T, index: int): int {.used.} =
    x.val
  proc `[]=`(x: var T, index: int, val: int) {.used.} =
    x.val = val
  proc `{}`(x: T, index: int): int {.used.} =
    x.val
  proc `{}=`(x: var T, index: int, val: int) {.used.} =
    x.val = val

block open_and_closed_in_templates:
  template templ1() =
    # the operators are "open" by by default ...
    var x: Obj
    x[1] = 1
    doAssert x[1] == 1
    x{1} = 2
    doAssert x{1} == 2

  generateOperators(Obj, i) # generate the operators to use
  templ1()

  template templ2() =
    # ... but can be requested to be closed
    bind `[]`, `[]=`, `{}`, `{}=`
    var x: Obj
    x[1] = 1
    doAssert x[1] == 1
    x{1} = 2
    doAssert x{1} == 2

  # generate overloads that, if considered, would lead to ambiguity errors
  generateOperators(Obj, j)
  # works; the overloads defined after the template are not considered
  templ2()

block mixin_in_templates:
  # define the operators for a different type:
  generateOperators(Other, i)

  template templ() =
    mixin `[]`, `[]=`, `{}`, `{}=`
    var x: Obj
    x[1] = 1
    doAssert x[1] == 1
    x{1} = 2
    doAssert x{1} == 2

  # define the real operators to use:
  generateOperators(Obj, i)
  templ() # works

block open_and_closed_in_generics:
  proc p[T]() =
    # the operators are "closed" by default, so a ``mixin`` statement is
    # required (at least for the curly operator)
    mixin `[]`, `[]=`, `{}`, `{}=`
    var x: Obj
    x[1] = 1
    doAssert x[1] == 1
    x{1} = 2
    doAssert x{1} == 2

  generateOperators(Obj, i) # generate the operators to use

  p[int]()

  proc p2[T]() =
    # if identifiers refer to existing symbols, the default for subscript-like
    # overloads is currently "open" (this is different from the behaviour of
    # other overloads)
    bind `[]`, `[]=`, `{}`, `{}=`
    var x: Obj
    x[1] = 1
    doAssert x[1] == 1
    x{1} = 2
    doAssert x{1} == 2

  # generate overloads that, if considered, would lead to ambiguity errors
  generateOperators(Obj, j)
  # works; the overloads defined after the template are not considered
  p2[int]()

block mixin_in_templates:
  # define the operators for a different type:
  generateOperators(Other, i)

  template templ() =
    mixin `[]`, `[]=`, `{}`, `{}=`
    var x: Obj
    x[1] = 1
    doAssert x[1] == 1
    x{1} = 2
    doAssert x{1} == 2

  # define the real operators to use:
  generateOperators(Obj, i)
  templ()
