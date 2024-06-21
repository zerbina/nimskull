type
  Opcode* = enum
    opcNop

    # stack manipluation:
    opcDrop       ## x:any
    opcDup        ## num:imm32 -> *
    opcSwap       ## a:any b:any -> any, any

    opcLdConst    ## idx:int -> value
    opcLdImmInt   ## val:imm32 -> int
    opcLdImmFloat ## val:imm32 -> float

    # integer arithmetic operations
    opcAddImm     ## val:int val:imm32
    opcAddInt     ## a:int b:int -> int
    opcSubInt     ## a:int b:int -> int
    opcMulInt     ## a:int b:int -> int
    opcDivInt     ## a:int b:int -> int
    opcDivU       ## a:int b:int -> int
    opcModInt
    opcModU
    opcNegInt
    opcOffset     ## base:int idx:int mul:imm32 -> int

    # bit operations
    opcBitAnd
    opcBitOr
    opcBitXor
    opcBitNot     ## a:int -> int
    opcMask       ## a:int bits:imm8
    opcShr        ## a:int b:int -> int
    opcAshr       ## a:int b:int -> int
    opcShl        ## a:int b:int -> int
    opcSignExtend ## val:int width:imm8 -> int

    # checked signed integer arithmetic
    opcAddChck    ## a:int b:int width:imm8 -> res:int of:int
    opcSubChck    ## a:int b:int width:imm8 -> res:int of:int
    opcMulChck    ## a:int b:int width:imm8 -> res:int of:int
    opcDivChck    ## a:int b:int width:imm8 -> res:int of:int
    opcModChck    ## a:int b:int width:imm8 -> res:int of:int

    # float arithmetic
    opcAddFloat   ## a:float b:float -> float
    opcSubFloat
    opcMulFloat
    opcDivFloat
    opcNegFloat

    # boolean operations:
    opcEqInt ## a:int b:int -> int
    opcLtInt ## a:int b:int -> int
    opcLeInt ## a:int b:int
    opcLtu ## a:int b:int
    opcLeu ## a:int b:int
    opcEqFloat
    opcLtFloat
    opcLeFloat
    opcNot

    # conversion
    opcUIntToFloat ## val:int width:imm8   -> float
    opcFloatToUint ## val:float width:imm8 -> int
    opcSIntToFloat ## val:int width:imm8   -> float
    opcFloatToSInt ## val:float width:imm8 -> int
    opcReinterpF32 ## val:int -> float
    opcReinterpF64 ## val:int -> float
    opcReinterpI32 ## val:float -> int
    opcReinterpI64 ## val:float -> int

    # control-flow operations:
    opcBranch # cond:int invert:imm8
    opcJmp    # target:imm32
    opcRet    # val:val
    opcEnter, # rel:imm32
    opcLeave, # abort:imm8
    opcFinally, # relEnd:imm32
    opcFinallyEnd,
    opcRaise,   # val:int mode:imm8
    opcCall     # callee:imm32 num:imm16
    opcIndCall  # callee:int  typ:imm16 num:imm16
    opcIndCallCl # callee:int  typ:imm16 num:imm16 (call closure)

    # locals and globals:
    opcGetLocal  # idx:imm32
    opcSetLocal  # x:any idx:imm32 -> any
    opcPopLocal  # x:any idx:imm32
    opcGetGlobal # idx:imm32 primary:imm8

    # memory operations:
    opcLdInt8  # addr:int offset:imm32u
    opcLdInt16 # addr:int offset:imm32u
    opcLdInt32 # addr:int offset:imm32u
    opcLdInt64 # addr:int offset:imm32u

    opcLdFlt32 # addr:int offset:imm32u
    opcLdFlt64 # addr:int offset:imm32u

    opcWrInt8  # addr:int offset:imm32
    opcWrInt16 #
    opcWrInt32 #
    opcWrInt64 #
    opcWrFlt32 # addr:int offset:imm32u
    opcWrFlt64 # addr:int offset:imm32u

    opcWrRef   # addr:int offset:imm32

    opcMemCopy  # src:int dst:int len:int
    opcMemClear # dst:int len:int

    # set operations:
    opcEqSet
    opcLtSet
    opcLeSet
    opcMulSet
    opcPlusSet
    opcMinusSet
    opcInSet
    opcIncl      # addr:int val:int
    opcInclRange # addr:int lo:int hi:int
    opcExcl      # addr:int val:int

    # rtti-based operations
    opcCopy    # dst:int typ:imm32
    opcDestroy # dst:int typ:imm32
    opcReset   # dst:int typ:imm32
    opcCheck   # dst:int typ:imm32

    # allocation
    opcStackAlloc # typ:imm32
    opcTrim       # to:imm32

    opcYield # args:imm32 reason:imm8

  TOpcode* = Opcode
  AccessViolationReason* = enum
    avrNoError      ## No violation happened
    avrOutOfBounds  ## Access to an address not owned by the VM
    avrTypeMismatch ## Dynamic type is not compatible with static type
    avrNoLocation   ## Address points to valid VM memory. but not to the start
                    ## of a location
