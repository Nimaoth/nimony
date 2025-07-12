#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "license.txt", included in this
#    distribution, for details about the copyright.
#

# We produce WASM

import std / [assertions, syncio, tables, sets, intsets, strutils, options, strformat, genasts, macros]
from std / os import changeFileExt, splitFile, extractFilename

import .. / .. / lib / [bitabs, lineinfos, nifstreams, nifcursors]
import ".." / [nifc_model, typenav]

import wasm_builder

type
  LocalVariableStorage* = enum Local, Stack, LocalStackPointer
  LocalVariable* = object
    case kind*: LocalVariableStorage
    of Local, LocalStackPointer: localIdx*: WasmLocalIdx
    of Stack: stackOffset*: int32

  DestinationStorage* = enum Stack, Memory, Discard, LValue
  Destination* = object
    typ: Cursor
    case kind*: DestinationStorage
    of Stack:
      load: WasmInstrKind
    of Memory:
      store: WasmInstrKind
      offset*: uint32 # todo: remove?
      align*: uint32
      size*: int32
    of Discard: discard
    of LValue: discard

  # todo: better names
  TypeAttributes* = tuple[size: int32, align: int32, passReturnAsOutParam: bool]
  WasmTypeAttributes* = tuple[typ: WasmValueType, load: WasmInstrKind, store: WasmInstrKind]

  # TypeAttributeComputer* = proc(self: LanguageWasmCompilerExtension, typ: AstNode): TypeAttributes {.gcsafe, raises: [CatchableError].}
  # GeneratorFunc* = proc(self: LanguageWasmCompilerExtension, node: AstNode, dest: Destination) {.gcsafe, raises: [CatchableError].}
  # FunctionInputOutputComputer* = proc(self: LanguageWasmCompilerExtension, node: AstNode): tuple[inputs: seq[WasmValueType], outputs: seq[WasmValueType]] {.gcsafe, raises: [CatchableError].}
  # FunctionConstructorComputer* = proc(self: LanguageWasmCompilerExtension, node: AstNode, exportName: Option[string], inputs: seq[WasmValueType], outputs: seq[WasmValueType]): WasmFuncIdx {.gcsafe, raises: [CatchableError].}

  GeneratedCode* = object
    m: Module
    builder: WasmBuilder
    data: TokenBuf
    code: TokenBuf
    init: TokenBuf
    intmSize, inConst, labels, prologAt: int

    wasmFuncs: Table[SymId, WasmFuncIdx]

    functionsToCompile*: seq[(Cursor, WasmFuncIdx)]
    localIndices*: Table[SymId, LocalVariable]
    globalIndices*: Table[SymId, WasmGlobalIdx]
    labelIndices*: Table[Cursor, int] # Not the actual index
    wasmValueTypes*: Table[Cursor, WasmTypeAttributes]
    symTypes*: Table[SymId, Cursor]
    symTypeAttributes*: Table[SymId, TypeAttributes]
    symDestinations*: Table[SymId, Destination]
    # typeAttributes*: Table[ClassId, TypeAttributes]
    # typeAttributeComputers*: Table[ClassId, tuple[ext: LanguageWasmCompilerExtension, gen: TypeAttributeComputer]]
    # functionInputOutputComputer*: Table[ClassId, tuple[ext: LanguageWasmCompilerExtension, gen: FunctionInputOutputComputer]]
    # functionConstructors*: Table[ClassId, tuple[ext: LanguageWasmCompilerExtension, gen: FunctionConstructorComputer]]

    loopBranchIndices*: Table[Cursor, tuple[breakIndex: int, continueIndex: int]]
    functionTableIndices*: Table[Cursor, (WasmTableIdx, int32)]
    functionRefIndices: seq[WasmFuncIdx]
    functionRefTableIdx: WasmTableIdx

    exprStack*: seq[WasmExpr]
    currentExpr*: WasmExpr
    currentLocals*: seq[tuple[typ: WasmValueType, id: string]]
    currentParamCount*: int32
    currentStackLocals*: seq[int32]
    currentStackLocalsSize*: int32

    returnValueDestination*: Destination
    passReturnAsOutParam*: bool

    genDebugCode: bool

    # generators*: Table[ClassId, tuple[ext: LanguageWasmCompilerExtension, gen: GeneratorFunc]]
    # extensions: seq[LanguageWasmCompilerExtension]

    # imported
    printI32: WasmFuncIdx
    printU32: WasmFuncIdx
    printI64: WasmFuncIdx
    printU64: WasmFuncIdx
    printF32: WasmFuncIdx
    printF64: WasmFuncIdx
    printChar: WasmFuncIdx
    printString: WasmFuncIdx
    printLine: WasmFuncIdx
    intToString: WasmFuncIdx

    # implemented inline
    buildString: WasmFuncIdx
    strlen: WasmFuncIdx
    allocFunc: WasmFuncIdx
    cstrToInternal*: WasmFuncIdx

    stackSize: int32
    activeDataOffset: int32

    stackBase: WasmGlobalIdx
    stackEnd: WasmGlobalIdx
    stackPointer: WasmGlobalIdx

    currentBasePointer*: WasmLocalIdx

    memoryBase: WasmGlobalIdx
    tableBase: WasmGlobalIdx
    heapBase: WasmGlobalIdx
    heapSize: WasmGlobalIdx

    globalData: seq[uint8]

type
  TypeList = object
    processed: IntSet
    s: seq[Cursor]

  TypeOrder = object
    forwardedDecls, ordered: TypeList
    lookedAt: IntSet
    lookedAtBodies: HashSet[SymId]

# proc traverseObjectBody(m: Module; o: var TypeOrder; t: Cursor)

type
  VarKind = enum
    IsLocal, IsGlobal, IsThreadlocal, IsConst

proc `$`(s: SymId): string = $s.int

proc addStringData*(c: var GeneratedCode, value: string): int32 =
  let offset = c.globalData.len.int32
  c.globalData.add(value.toOpenArrayByte(0, value.high))
  c.globalData.add(0)

  result = offset + c.activeDataOffset

proc comment*(c: GeneratedCode, comment: string) =
  c.currentExpr.instr.add WasmInstr(kind: Comment, comment: comment)

macro instr*(c: WasmExpr, op: WasmInstrKind, args: varargs[untyped]): untyped =
  result = genAst(c, op):
    c.instr.add WasmInstr(kind: op)
  for arg in args:
    result[1].add arg

macro instr*(c: GeneratedCode, op: WasmInstrKind, args: varargs[untyped]): untyped =
  result = genAst(c, op):
    c.currentExpr.instr.add WasmInstr(kind: op)
  for arg in args:
    result[1].add arg

# proc genDup*(c: GeneratedCode, typ: AstNode) =
#   let tempIdx = c.getTempLocal(typ)
#   c.instr(LocalTee, localIdx: tempIdx)
#   c.instr(LocalGet, localIdx: tempIdx)

proc storeInstr*(c: GeneratedCode, op: WasmInstrKind, offset: uint32, align: uint32) =
  # debugf"storeInstr {op}, offset {offset}, align {align}"
  assert op in {I32Store, I64Store, F32Store, F64Store, I32Store8, I64Store8, I32Store16, I64Store16, I64Store32}
  var instr = WasmInstr(kind: op)
  instr.memArg = WasmMemArg(offset: offset, align: align)
  c.currentExpr.instr.add instr

proc loadInstr*(c: GeneratedCode, op: WasmInstrKind, offset: uint32, align: uint32) =
  # debugf"loadInstr {op}, offset {offset}, align {align}"
  assert op in {I32Load, I64Load, F32Load, F64Load, I32Load8U, I32Load8S, I64Load8U, I64Load8S, I32Load16U, I32Load16S, I64Load16U, I64Load16S, I64Load32U, I64Load32S}
  var instr = WasmInstr(kind: op)
  instr.memArg = WasmMemArg(offset: offset, align: align)
  c.currentExpr.instr.add instr

proc initGeneratedCode*(m: sink Module; intmSize: int): GeneratedCode =
  result = GeneratedCode(m: m, intmSize: intmSize)

proc error(m: Module; msg: string; n: Cursor) {.noreturn.} =
  let info = n.info
  if info.isValid:
    let rawInfo = unpack(pool.man, info)
    if rawInfo.file.isValid:
      write stdout, pool.files[rawInfo.file]
      write stdout, "(" & $rawInfo.line & ", " & $(rawInfo.col+1) & ") "
  write stdout, "[Error] "
  write stdout, msg
  writeLine stdout, toString(n, false)
  when defined(debug):
    echo getStackTrace()
  # quit 1

proc `$`(dest: Destination): string =
  case dest.kind
  of DestinationStorage.Stack: &"Stack"
  of DestinationStorage.Memory: &"Memory(off: {dest.offset}, align: {dest.align}, size: {dest.size}, {dest.store})"
  of DestinationStorage.Discard: &"Discard"
  of DestinationStorage.LValue: &"LValue"

proc `$`(local: LocalVariable): string =
  case local.kind
  of Local: &"Local({local.localIdx})"
  of LocalStackPointer: &"LocalStackPointer({local.localIdx})"
  of Stack: &"Stack({local.stackOffset})"

proc align*[T](address, alignment: T): T =
  if alignment == 0: # Actually, this is illegal. This branch exists to actively
                     # hide problems.
    result = address
  else:
    result = (address + (alignment - 1)) and not (alignment - 1)

proc genStmt(c: var GeneratedCode; n: var Cursor, dest: Destination)
proc genx(c: var GeneratedCode; n: var Cursor, dest: Destination)
proc genLvalue(c: var GeneratedCode; n: var Cursor, dest: Destination)

proc toWasmValueType*(c: GeneratedCode, typ: Cursor): Option[WasmValueType] =
  var n = typ

  case n.typeKind
  of VoidT:
    result = WasmValueType.none
  of IT:
    inc n
    let bits = pool.integers[n.intId].int32
    if bits == -1:
      result = WasmValueType.I32.some
    else:
      let bytes = bits div 8
      if bytes <= 4:
        result = WasmValueType.I32.some
      else:
        result = WasmValueType.I64.some
  of UT:
    inc n
    let bits = pool.integers[n.intId].int32
    if bits == -1:
      result = WasmValueType.I32.some
    else:
      let bytes = bits div 8
      if bytes <= 4:
        result = WasmValueType.I32.some
      else:
        result = WasmValueType.I64.some
  of FT:
    inc n
    let bits = pool.integers[n.intId].int32
    if bits == -1:
      result = WasmValueType.F32.some
    else:
      let bytes = bits div 8
      if bytes <= 4:
        result = WasmValueType.F32.some
      else:
        result = WasmValueType.F64.some
  of BoolT:
    result = WasmValueType.I32.some
  of CT:
    inc n
    result = WasmValueType.I32.some
  of NoType:
    if n.kind == Symbol:
      # todo
      result = WasmValueType.none
      inc n
    elif n.kind == IntLit:
      result = WasmValueType.I32.some
      inc n
    else:
      error c.m, "node is not a type: ", n
  # of PtrT, APtrT:
  #   atomPointer(c, n, name, isConst)
  # of FlexarrayT:
  #   inc n
  #   genType c, n
  #   maybeAddName(c, name, isConst)
  #   c.add BracketLe
  #   c.add BracketRi
  #   skipParRi n
  # of ProctypeT:
  #   genProcType(c, n, name, isConst)
  # of ParamsT, UnionT, ObjectT, EnumT, ArrayT:
  #   error c.m, "nominal type not allowed here: ", n
  # defer:
  #   echo &"getTypeAttributes {typ} -> {result}"
  # todo
  # c.typeAttributes.withValue(typ.class, val):
  #   return val[]
  # c.typeAttributeComputers.withValue(typ.class, val):
  #   return val[].gen(val[].ext, typ)
  else:
    # if c.wasmValueTypes.contains(typ):
    #   return c.wasmValueTypes[typ].typ.some
    # log lvlError, fmt"toWasmValueType: Type not implemented: {`$`(typ, true)}"
    return WasmValueType.none

proc getTypeAttributes*(c: GeneratedCode, typ: Cursor): TypeAttributes {.raises: [CatchableError].} =
  var n = typ
  case n.typeKind
  of VoidT:
    result = (0, 1, false)
  of IT:
    inc n
    let bits = pool.integers[n.intId].int32
    if bits == -1:
      result = (4, 4, false)
    else:
      let bytes = bits div 8
      result = (bytes, bytes, false)
  of UT:
    inc n
    let bits = pool.integers[n.intId].int32
    if bits == -1:
      result = (4, 4, false)
    else:
      let bytes = bits div 8
      result = (bytes, bytes, false)
  of FT:
    inc n
    let bits = pool.integers[n.intId].int32
    if bits == -1:
      result = (4, 4, false)
    else:
      let bytes = bits div 8
      result = (bytes, bytes, false)
  of BoolT:
    result = (1, 1, false)
  of CT:
    inc n
    let bytes = pool.integers[n.intId].int32 div 8
    result = (bytes, bytes, false)
  of NoType:
    if n.kind == Symbol:
      # atom(c, mangle(pool.syms[n.symId]), name, isConst)
      result = (0, 1, false)
      inc n
    elif n.kind == IntLit:
      result = (4, 4, false)
      inc n
    else:
      error c.m, "node is not a type: ", n
  # of PtrT, APtrT:
  #   atomPointer(c, n, name, isConst)
  # of FlexarrayT:
  #   inc n
  #   genType c, n
  #   maybeAddName(c, name, isConst)
  #   c.add BracketLe
  #   c.add BracketRi
  #   skipParRi n
  # of ProctypeT:
  #   genProcType(c, n, name, isConst)
  # of ParamsT, UnionT, ObjectT, EnumT, ArrayT:
  #   error c.m, "nominal type not allowed here: ", n
  # defer:
  #   echo &"getTypeAttributes {typ} -> {result}"
  # todo
  # c.typeAttributes.withValue(typ.class, val):
  #   return val[]
  # c.typeAttributeComputers.withValue(typ.class, val):
  #   return val[].gen(val[].ext, typ)
  else:
    result = (0, 1, false)

  # echo &"getTypeAttributes {typ} -> {result}"

proc getTypeMemInstructions*(c: GeneratedCode, typ: Cursor): tuple[load: WasmInstrKind, store: WasmInstrKind] =
  if c.wasmValueTypes.contains(typ):
    let (_, load, store) = c.wasmValueTypes[typ]
    return (load, store)

  var n = typ
  case n.typeKind
  of VoidT:
    result = (I32Load, I32Store)
  of IT:
    inc n
    let bits = pool.integers[n.intId].int32
    if bits == -1:
      result = (I32Load, I32Store)
    else:
      let bytes = bits div 8
      if bytes <= 4:
        result = (I32Load, I32Store)
      else:
        result = (I64Load, I64Store)
  of UT:
    inc n
    let bits = pool.integers[n.intId].int32
    if bits == -1:
      result = (I32Load, I32Store)
    else:
      let bytes = bits div 8
      if bytes <= 4:
        result = (I32Load, I32Store)
      else:
        result = (I64Load, I64Store)
  of FT:
    inc n
    let bits = pool.integers[n.intId].int32
    if bits == -1:
      result = (F32Load, F32Store)
    else:
      let bytes = bits div 8
      if bytes <= 4:
        result = (F32Load, F32Store)
      else:
        result = (F64Load, F64Store)
  of BoolT:
    result = (I32Load, I32Store)
  of CT:
    inc n
    result = (I32Load, I32Store)
  of NoType:
    if n.kind == Symbol:
      result = (I32Load, I32Store)
      inc n
    elif n.kind == IntLit:
      result = (I32Load, I32Store)
      inc n
    else:
      error c.m, "node is not a type: ", n
  # of PtrT, APtrT:
  #   atomPointer(c, n, name, isConst)
  # of FlexarrayT:
  #   inc n
  #   genType c, n
  #   maybeAddName(c, name, isConst)
  #   c.add BracketLe
  #   c.add BracketRi
  #   skipParRi n
  # of ProctypeT:
  #   genProcType(c, n, name, isConst)
  # of ParamsT, UnionT, ObjectT, EnumT, ArrayT:
  #   error c.m, "nominal type not allowed here: ", n
  # defer:
  #   echo &"getTypeAttributes {typ} -> {result}"
  # todo
  # c.typeAttributes.withValue(typ.class, val):
  #   return val[]
  # c.typeAttributeComputers.withValue(typ.class, val):
  #   return val[].gen(val[].ext, typ)
  else:
    result = (I32Load, I32Store)

    error c.m, &"getTypeMemInstructions: Type not implemented: ", typ

proc genStoreDestination*(c: var GeneratedCode, dest: Destination) {.raises: [CatchableError].} =
  case dest.kind
  of Stack: discard
  of Memory:
    c.storeInstr(dest.store, dest.offset, dest.align)
  of Discard:
    c.instr(Drop)
    discard
  else:
    discard

proc shouldPassAsOutParamater*(c: GeneratedCode, typ: Cursor): bool {.raises: [CatchableError].} =
  if typ.kind == DotToken:
    return false

  let (size, _, passReturnAsOutParam) = c.getTypeAttributes(typ)
  if passReturnAsOutParam:
    return true
  if size > 8:
    return true
  return false

proc createLocal*(c: var GeneratedCode, id: SymId, typ: Cursor, name: string): WasmLocalIdx =
  result = 0.WasmLocalIdx
  let wasmType = c.toWasmValueType(typ)
  if wasmType.isSome:
    result = (c.currentLocals.len + c.currentParamCount).WasmLocalIdx
    c.currentLocals.add((wasmType.get, name))
    c.localIndices[id] = LocalVariable(kind: Local, localIdx: result)

proc createStackLocal*(c: var GeneratedCode, id: SymId, typ: Cursor): int32 {.raises: [CatchableError].} =
  # echo &"createStackLocal {pool.syms[id]}, {typ}"
  let (size, alignment, _) = c.getTypeAttributes(typ)

  c.currentStackLocalsSize = c.currentStackLocalsSize.align(alignment)
  result = c.currentStackLocalsSize

  c.currentStackLocals.add(c.currentStackLocalsSize)
  # debugf"createStackLocal size {size}, alignment {alignment}, offset {c.currentStackLocalsSize}"

  c.localIndices[id] = LocalVariable(kind: Stack, stackOffset: c.currentStackLocalsSize)

  c.currentStackLocalsSize += size

proc getFunctionTypeInputOutput(c: GeneratedCode, prc: ProcDecl): tuple[inputs: seq[WasmValueType], outputs: seq[WasmValueType]] =
  result = (@[], @[])
  if prc.returnType.kind != DotToken:
    if c.shouldPassAsOutParamater(prc.returnType):
      result.inputs.add WasmValueType.I32
    else:
      result.outputs.add c.toWasmValueType(prc.returnType).get

  var params = 0
  if prc.params.kind != DotToken:
    var p = prc.params.firstSon
    while p.kind != ParRi:
      var d = takeParamDecl(p)
      if d.name.kind == SymbolDef:
        # let lit = d.name.symId
        # c.m.registerLocal(lit, d.typ)
        # let name = mangle(pool.syms[lit])
        # genType c, d.typ, name
        # genParamPragmas c, d.pragmas
        if c.shouldPassAsOutParamater(d.typ):
          result.inputs.add WasmValueType.I32
        else:
          result.inputs.add c.toWasmValueType(d.typ).get

      else:
        error c.m, "expected SymbolDef but got: ", d.name

      inc params
    skipParRi p

template genNested*(c: var GeneratedCode, body: untyped): untyped =
  c.exprStack.add c.currentExpr
  c.currentExpr = WasmExpr()

  try:
    body
  finally:
    let bodyExpr = c.currentExpr
    c.currentExpr = c.exprStack.pop
    c.instr(Loop, loopType: typ, loopInstr: move bodyExpr.instr)

template genBlock*(c: var GeneratedCode, typ: WasmBlockType, body: untyped): untyped =
  c.exprStack.add c.currentExpr
  c.currentExpr = WasmExpr()

  try:
    body
  finally:
    let bodyExpr = c.currentExpr
    c.currentExpr = c.exprStack.pop
    c.instr(Block, blockType: typ, blockInstr: move bodyExpr.instr)

template genLoop*(c: var GeneratedCode, typ: WasmBlockType, body: untyped): untyped =
  c.exprStack.add c.currentExpr
  c.currentExpr = WasmExpr()

  try:
    body
  finally:
    let bodyExpr = c.currentExpr
    c.currentExpr = c.exprStack.pop
    c.instr(Loop, loopType: typ, loopInstr: move bodyExpr.instr)

# proc genType(c: var GeneratedCode; n: var Cursor; name = ""; isConst = false) =
#   case n.typeKind
#   of VoidT:
#     atom(c, "void", name, isConst)
#     skip n
#   of IT:
#     atomNumber(c, n, "NI", name, isConst)
#   of UT:
#     atomNumber(c, n, "NU", name, isConst)
#   of FT:
#     atomNumber(c, n, "NF", name, isConst)
#   of BoolT:
#     atomNumber(c, n, "NB8", name, isConst, isBool = true)
#   of CT:
#     atomNumber(c, n, "NC", name, isConst)
#   of NoType:
#     if n.kind == Symbol:
#       atom(c, mangle(pool.syms[n.symId]), name, isConst)
#       inc n
#     else:
#       error c.m, "node is not a type: ", n
#   of PtrT, APtrT:
#     atomPointer(c, n, name, isConst)
#   of FlexarrayT:
#     inc n
#     genType c, n
#     maybeAddName(c, name, isConst)
#     c.add BracketLe
#     c.add BracketRi
#     skipParRi n
#   of ProctypeT:
#     genProcType(c, n, name, isConst)
#   of ParamsT, UnionT, ObjectT, EnumT, ArrayT:
#     error c.m, "nominal type not allowed here: ", n

proc genProcSig(c: var GeneratedCode; n: var Cursor; isExtern: bool) =
  # echo &"genProcSig {n}"
  var prc = takeProcDecl(n)
  assert prc.name.kind == SymbolDef
  let name = pool.syms[prc.name.symId]

  var lastCallConv = NoCallConv

  let (inputs, outputs) = if lastCallConv != NoCallConv:
    # c.add callingConvToStr(lastCallConv)
    # if prc.returnType.kind == DotToken:
    #   c.add "void"
    # else:
    #   genType c, prc.returnType
    (@[], @[])
  else:
    c.getFunctionTypeInputOutput(prc)

  if name.endsWith(".c") or true:
    let funcIdx = c.builder.addFunction(inputs, outputs, name[0..^3].some)
    c.wasmFuncs[prc.name.symId] = funcIdx
  else:
    let funcIdx = c.builder.addFunction(inputs, outputs)
    c.wasmFuncs[prc.name.symId] = funcIdx

proc genImp(c: var GeneratedCode; n: var Cursor) =
  inc(n)
  var prc = takeProcDecl(n)
  assert prc.name.kind == SymbolDef
  let name = pool.syms[prc.name.symId]

  var lastCallConv = NoCallConv

  let (inputs, outputs) = if lastCallConv != NoCallConv:
    # c.add callingConvToStr(lastCallConv)
    # if prc.returnType.kind == DotToken:
    #   c.add "void"
    # else:
    #   genType c, prc.returnType
    (@[], @[])
  else:
    c.getFunctionTypeInputOutput(prc)

  assert name.endsWith(".c")
  let backslash = name.find("\\")
  let (env, funcName) = if backslash == -1:
    ("env", name)
  else:
    (name[0..<backslash], name[backslash + 1..^1])
  c.wasmFuncs[prc.name.symId] = c.builder.addImport(env, funcName[0..^3], inputs, outputs)

  skipParRi n

proc genProcDecl(c: var GeneratedCode; n: var Cursor; isExtern: bool) =
  # echo &"genProcDecl {n}"
  var prc = takeProcDecl(n)
  assert prc.name.kind == SymbolDef

  let name = pool.syms[prc.name.symId]
  let funcIdx = c.wasmFuncs[prc.name.symId]

  var lastCallConv = NoCallConv

  c.currentExpr = WasmExpr()
  c.localIndices.clear()
  c.currentLocals.setLen 0
  c.currentStackLocalsSize = 0
  c.currentParamCount = 0.int32

  let passReturnAsOutParam = c.shouldPassAsOutParamater(prc.returnType)
  if passReturnAsOutParam:
    c.localIndices[0.SymId] = LocalVariable(kind: Local, localIdx: c.currentParamCount.WasmLocalIdx)
    inc c.currentParamCount

  if prc.params.kind != DotToken:
    var p = prc.params.firstSon
    while p.kind != ParRi:
      var d = takeParamDecl(p)
      if d.name.kind == SymbolDef:
        c.symTypes[d.name.symId] = d.typ
        c.symTypeAttributes[d.name.symId] = c.getTypeAttributes(d.typ)
        if c.shouldPassAsOutParamater(d.typ):
          c.localIndices[d.name.symId] = LocalVariable(kind: LocalStackPointer, localIdx: c.currentParamCount.WasmLocalIdx)
        else:
          c.localIndices[d.name.symId] = LocalVariable(kind: Local, localIdx: c.currentParamCount.WasmLocalIdx)
          c.symDestinations[d.name.symId] = Destination(kind: Stack, load: c.getTypeMemInstructions(d.typ).load)

      else:
        error c.m, "expected SymbolDef but got: ", d.name

      inc c.currentParamCount
    skipParRi p

  c.currentBasePointer = (c.currentLocals.len + c.currentParamCount).WasmLocalIdx
  c.currentLocals.add((I32, "__base_pointer")) # base pointer

  let stackSizeInstrIndex = block: # prologue
    c.comment("prologue")
    c.instr(GlobalGet, globalIdx: c.stackPointer)
    c.instr(I32Const, i32Const: 0) # size, patched at end when we know the size of locals
    let i = c.currentExpr.instr.high
    c.instr(I32Sub)
    c.instr(LocalTee, localIdx: c.currentBasePointer)
    c.instr(GlobalSet, globalIdx: c.stackPointer)
    i

  # todo: check stack pointer?
  # c.instr(GlobalGet, globalIdx: c.stackPointer)
  # c.instr(I32Const, i32Const: 0)
  # c.instr(I32LeS)
  # c.instr(If, ifType: WasmBlockType(kind: ValType, typ: WasmValueType.none),
  #   ifThenInstr: @[WasmInstr(kind: Unreachable)],
  #   ifElseInstr: @[])

  let destination = if prc.returnType.kind == DotToken:
    Destination(kind: Discard)
  elif passReturnAsOutParam:
    c.instr(LocalGet, localIdx: 0.WasmLocalIdx) # load return value address from first parameter
    Destination(kind: Memory, offset: 0, align: 0, size: c.getTypeAttributes(prc.returnType).size, store: c.getTypeMemInstructions(prc.returnType).store)
  else:
    Destination(kind: Stack, load: c.getTypeMemInstructions(prc.returnType).load)

  c.returnValueDestination = destination
  c.passReturnAsOutParam = passReturnAsOutParam

  c.comment("body")
  genStmt c, prc.body, destination

  let requiredStackSize: int32 = c.currentStackLocalsSize
  c.currentExpr.instr[stackSizeInstrIndex].i32Const = requiredStackSize

  # epilogue
  c.comment("epilogue")
  c.instr(LocalGet, localIdx: c.currentBasePointer)
  c.instr(I32Const, i32Const: requiredStackSize)
  c.instr(I32Add)
  c.instr(GlobalSet, globalIdx: c.stackPointer)

  c.builder.setBody(funcIdx, c.currentLocals, c.currentExpr)

proc genVarInitValue(c: var GeneratedCode; n: var Cursor, dest: Destination) =
  discard
  if n.kind == DotToken:
    inc n
  elif n.stmtKind == OnErrS:
    error c.m, "not implemented genVarInitValue OnErrS", n
  else:
    genx c, n, dest

proc genVarDecl(c: var GeneratedCode; n: var Cursor; vk: VarKind; toExtern = false) =
  # echo &"genVarDecl {vk}, {n}"
  var d = takeVarDecl(n)

  if d.name.kind == SymbolDef:
    let symId = d.name.symId
    # echo &"{pool.syms[symId]} -> {d.typ}, {toExtern}, {d.value.kind}"
    let typeAttributes = c.getTypeAttributes(d.typ)
    c.symTypes[symId] = d.typ
    c.symTypeAttributes[symId] = typeAttributes

    if not toExtern:
      let offset = c.createStackLocal(symId, d.typ)
      let dest = Destination(
        kind: Memory,
        offset: 0,
        align: 0,
        size: typeAttributes.size,
        store: c.getTypeMemInstructions(d.typ).store,
      )

      c.symDestinations[symId] = dest

      if d.value.kind != DotToken:
        c.instr(LocalGet, localIdx: c.currentBasePointer)
        if offset > 0:
          c.instr(I32Const, i32Const: offset.int32)
          c.instr(I32Add)

        genVarInitValue c, d.value, dest

  else:
    error c.m, "expected SymbolDef but got: ", d.name

proc genVar(c: var GeneratedCode; n: var Cursor; vk: VarKind; toExtern = false) =
  case vk
  of IsLocal:
    genVarDecl c, n, IsLocal, toExtern
  of IsGlobal:
    # moveToDataSection:
    genVarDecl c, n, IsGlobal, toExtern
  of IsThreadlocal:
  # moveToDataSection:
    genVarDecl c, n, IsThreadlocal, toExtern
  of IsConst:
    # moveToDataSection:
    genVarDecl c, n, IsConst, toExtern

proc genCall(c: var GeneratedCode; n: var Cursor, dest: Destination) =
  # genCLineDir(c, info(n))
  echo &"genCall {n}"
  inc n
  let isCfn = isImportC(n)

  let fun = n

  # let returnType = c.ctx.computeType(node)
  let passReturnAsOutParam = false # c.shouldPassAsOutParamater(returnType)

  if passReturnAsOutParam:
    case dest.kind
    of Stack: return # todo error
    of Memory:
      if dest.offset > 0:
        echo fmt"test: apply offset for return value (not really an error)"
        c.instr(I32Const, i32Const: dest.offset.int32)
        c.instr(I32Add)
    of Discard: discard
    of LValue: return # todo error

  var i = 0
  while n.kind != ParRi:
    let passByReference = false # c.shouldPassAsOutParamater(argType)
    let argDest = if passByReference:
      Destination(kind: LValue)
    else:
      Destination(kind: Stack)

    genx c, n, argDest
    inc i

  if fun.kind == Symbol:
    let funcIdx = c.wasmFuncs[fun.symId]
    c.instr(Call, callFuncIdx: funcIdx)

    let typ = c.builder.getFunctionType(funcIdx)
    if typ.output.types.len > 0: # not returnVoid and not passReturnAsOutParam:
      c.genStoreDestination(dest)
  else:
    var n2 = fun
    genx c, n2, dest

    if true: # not returnVoid and not passReturnAsOutParam:
      c.genStoreDestination(dest)

  skipParRi n

proc genStmt(c: var GeneratedCode; n: var Cursor, dest: Destination) =
  echo &"genStmt {n}"
  c.comment(($n).splitLines[0])

  case n.stmtKind
  of NoStmt:
    if n.kind == DotToken:
      inc n
    else:
      error c.m, "expected statement but got: ", n
      inc n

  of StmtsS:
    inc n
    while n.kind != ParRi:
      genStmt(c, n, dest)
    inc n # ParRi

  of CallS:
    genCall c, n, Destination(kind: Discard)

  of VarS:
    genVar c, n, IsLocal
  of GvarS:
    genVar c, n, IsGlobal
  of TvarS:
    genVar c, n, IsThreadlocal
  of ConstS:
    genVar c, n, IsConst

  of AsgnS:
    inc n
    var valueDest = Destination(kind: Stack)

    let target = n
    if target.kind == Symbol and target.symId in c.symDestinations:
      genLvalue c, n, Destination(kind: LValue)
      valueDest = c.symDestinations[target.symId]

    else:
      # genLvalue c, n, Destination(kind: LValue)
      # valueDest = Destination(kind: Memory, offset: 0, align: 0, size: 4, store: I32Store) # todo: figure out store instruction/size
      error c.m, "genStmt AsgnS: not implemented ", n

    genx c, n, valueDest
    skipParRi n

    # if target.kind == SymbolDef:
    #   case c.localIndices[id.get]
    #   of Local(localIdx: @index):
    #     c.instr(LocalSet, localIdx: index)
    #   of LocalStackPointer():
    #     discard
    #   of Stack():
    #     discard

    # assert dest.kind == Discard

  of DiscardS:
    inc n
    genStmt c, n, Destination(kind: Discard)

  of RetS:
    inc n
    if n.kind != DotToken:
      if c.passReturnAsOutParam:
        c.instr(LocalGet, localIdx: 0.WasmLocalIdx) # load return value address from first parameter
      c.genx n, c.returnValueDestination
    else:
      inc n
    # let actualIndex = WasmLabelIdx(c.exprStack.high)
    # c.instr(Br, brLabelIdx: actualIndex)
    skipParRi n
  else:
    error c.m, "genStmt: not implemented ", n
    inc n

const IdInt32 = ("i", 32)
const IdInt64 = ("i", 64)
const IdUInt32 = ("i", 32)
const IdUInt64 = ("i", 64)
const IdFloat32 = ("i", 32)
const IdFloat64 = ("i", 64)

const conversionOps = toTable {
  (IdInt32, IdInt64): I32WrapI64,
  (IdInt32, IdUInt64): I32WrapI64,
  (IdInt32, IdFloat32): I32TruncF32S,
  (IdInt32, IdFloat64): I32TruncF64S,

  (IdUInt32, IdInt64): I32WrapI64,
  (IdUInt32, IdUInt64): I32WrapI64,
  (IdUInt32, IdFloat32): I32TruncF32U,
  (IdUInt32, IdFloat64): I32TruncF64U,
  # (IdInt32, IdInt32): I32TruncSatF32S,
  # (IdInt32, IdInt32): I32TruncSatF32U,
  # (IdInt32, IdInt32): I32TruncSatF64S,
  # (IdInt32, IdInt32): I32TruncSatF64U,
  (IdInt64, IdInt32): I64ExtendI32S,
  (IdInt64, IdUInt32): I64ExtendI32U,
  (IdInt64, IdFloat32): I64TruncF32S,
  (IdInt64, IdFloat64): I64TruncF64S,

  (IdUInt64, IdInt32): I64ExtendI32S,
  (IdUInt64, IdUInt32): I64ExtendI32U,
  (IdUInt64, IdFloat32): I64TruncF32U,
  (IdUInt64, IdFloat64): I64TruncF64U,
  # (IdInt64, IdFloat32): I64TruncSatF32S,
  # (IdUInt64, IdFloat32): I64TruncSatF32U,
  # (IdInt64, IdFloat64): I64TruncSatF64S,
  # (IdUInt64, IdFloat64): I64TruncSatF64U,
  (IdFloat32, IdInt32): F32ConvertI32S,
  (IdFloat32, IdUInt32): F32ConvertI32U,
  (IdFloat32, IdInt64): F32ConvertI64S,
  (IdFloat32, IdUInt64): F32ConvertI64U,
  (IdFloat32, IdFloat64): F32DemoteF64,
  (IdFloat64, IdInt32): F64ConvertI32S,
  (IdFloat64, IdUInt32): F64ConvertI32U,
  (IdFloat64, IdInt64): F64ConvertI64S,
  (IdFloat64, IdUInt64): F64ConvertI64U,
  (IdFloat64, IdFloat32): F64PromoteF32,
  # (IdInt32, IdInt32): I32Extend8S,
  # (IdInt32, IdInt32): I32Extend16S,
  # (IdInt64, IdInt32): I64Extend8S,
  # (IdInt64, IdInt32): I64Extend16S,
  # (IdInt64, IdInt32): I64Extend32S,
}

# let reinterpretOps = toTable {
#   (IdInt32, IdFloat32): I32ReinterpretF32,
#   (IdUInt32, IdFloat32): I32ReinterpretF32,
#   (IdInt64, IdFloat64): I64ReinterpretF64,
#   (IdUInt64, IdFloat64): I64ReinterpretF64,
#   (IdFloat32, IdInt32): F32ReinterpretI32,
#   (IdFloat32, IdUInt32): F32ReinterpretI32,
#   (IdFloat64, IdInt64): F64ReinterpretI64,
#   (IdFloat64, IdUInt64): F64ReinterpretI64,
# }

proc genConv(c: var GeneratedCode; n: var Cursor, dest: Destination) =
  echo &"genConv {dest} {n}, {n.kind}, {n.exprKind}"
  inc n # (

  var typ = n
  skip n

  let expr = n

  case n.exprKind
  of NoExpr:
    let wasmType = c.toWasmValueType(typ)
    case n.kind
    of IntLit:
      if wasmType == I32.some:
        c.instr(I32Const, i32Const: pool.integers[expr.intId].int32)
      elif wasmType == I64.some:
        c.instr(I64Const, i64Const: pool.integers[expr.intId].int64)
      else:
        discard # todo: error
      c.genStoreDestination(dest)
      inc n
    of UIntLit:
      if wasmType == I32.some:
        c.instr(I32Const, i32Const: pool.uintegers[expr.uintId].int32)
      elif wasmType == I64.some:
        c.instr(I64Const, i64Const: pool.uintegers[expr.uintId].int64)
      else:
        discard # todo: error
      c.genStoreDestination(dest)
      inc n
    of FloatLit:
      if wasmType == F32.some:
        c.instr(F32Const, f32Const: pool.floats[expr.floatId].float32)
      elif wasmType == F64.some:
        c.instr(F64Const, f64Const: pool.floats[expr.floatId].float64)
      else:
        discard # todo: error
      c.genStoreDestination(dest)
      inc n
    of CharLit:
      let ch = expr.charLit
      c.instr(I32Const, i32Const: ch.int32)
      c.genStoreDestination(dest)
      inc n
    else:
      genx c, n, dest

  else:
    genx c, n, dest

    # let t1 =
    # if conversionOps.contains((targetType.class, sourceType.class)):
    #   let op = conversionOps[(targetType.class, sourceType.class)]
    #   self.compiler.currentExpr.instr.add WasmInstr(kind: op)

  skipParRi n

proc genLvalue(c: var GeneratedCode; n: var Cursor, dest: Destination) =
  echo &"genLvalue {dest} {n}, {n.kind}, {n.exprKind}"
  let expr = n
  var symId: SymId = SymId.default
  case n.exprKind
  of NoExpr:
    if n.kind == Symbol:
      symId = n.symId
      inc n
    else:
      error c.m, "expected expression but got: ", n
      return
  # of DerefC: genDeref c, n
  # of AtC:
  #   inc n
  #   let arrType = getType(c.m, n)
  #   genx c, n
  #   if not (c.m.isImportC(arrType) or arrType.typeKind == NoType):
  #     c.add Dot
  #     c.add "a"
  #   c.add BracketLe
  #   genx c, n
  #   c.add BracketRi
  #   skipParRi n
  # of PatC:
  #   inc n
  #   genx c, n
  #   c.add BracketLe
  #   genx c, n
  #   c.add BracketRi
  #   skipParRi n
  # of DotC:
  #   inc n
  #   genx c, n
  #   var fld = n
  #   skip n
  #   if n.kind == IntLit:
  #     var inh = pool.integers[n.intId]
  #     inc n
  #     while inh > 0:
  #       c.add ".Q"
  #       dec inh
  #   c.add Dot
  #   genx c, fld
  #   skipParRi n
  # of ErrvC:
  #   if {gfMainModule, gfHasError} * c.flags == {}:
  #     moveToDataSection:
  #       c.add ExternKeyword
  #       c.add ThreadVarToken
  #       c.add "NB8 "
  #       c.add ErrToken
  #       c.add Semicolon
  #     c.flags.incl gfHasError
  #   c.add ErrToken
  #   skip n
  # of OvfC:
  #   c.add OvfToken
  #   c.currentProc.needsOverflowFlag = true
  #   skip n
  else:
    error c.m, "not implemented genLvalue " & $expr.kind & ", ", expr
    return

  if symId notin c.localIndices:
    error c.m, "unknown local variable symbol ", expr
    return

  echo &"store {c.localIndices[symId]} in {dest}"
  let local = c.localIndices[symId]
  case dest.kind
  of Stack:
    case local.kind
    of Local:
      c.instr(LocalGet, localIdx: local.localIdx)

    of LocalStackPointer:
      c.instr(LocalGet, localIdx: local.localIdx)
      c.loadInstr(dest.load, 0, 0)

    of Stack:
      c.instr(LocalGet, localIdx: c.currentBasePointer)
      c.loadInstr(dest.load, local.stackOffset.uint32, 0)

  of Memory:
    case local.kind
    of Local:
      c.instr(LocalGet, localIdx: local.localIdx)
      c.storeInstr(dest.store, dest.offset, dest.align)

    of LocalStackPointer:
      c.instr(LocalGet, localIdx: local.localIdx)
      c.instr(I32Const, i32Const: dest.size)
      c.instr(MemoryCopy)

    of Stack:
      c.instr(LocalGet, localIdx: c.currentBasePointer)
      if local.stackOffset > 0:
        c.instr(I32Const, i32Const: local.stackOffset)
        c.instr(I32Add)
      c.instr(I32Const, i32Const: dest.size)
      c.instr(MemoryCopy)

  of Discard:
    discard

  of LValue:
    case local.kind
    of Local:
      error c.m, &"can't get lvalue of local: {pool.syms[symId]}, from here ", expr
    of LocalStackPointer:
      c.instr(LocalGet, localIdx: local.localIdx)
    of Stack:
      c.instr(LocalGet, localIdx: c.currentBasePointer)
      if local.stackOffset > 0:
        c.instr(I32Const, i32Const: local.stackOffset)
        c.instr(I32Add)

proc genSuffixNumber(c: var GeneratedCode; n: Cursor; suffix: Cursor, dest: Destination) =
  case pool.strings[suffix.litId]
  of "i64":
    c.instr(I64Const, i64Const: pool.integers[n.intId].int64)
  of "i32":
    c.instr(I32Const, i32Const: pool.integers[n.intId].int32)
  of "i16":
    c.instr(I32Const, i32Const: pool.integers[n.intId].int32)
  of "i8":
    c.instr(I32Const, i32Const: pool.integers[n.intId].int32)
  of "u64":
    c.instr(I64Const, i64Const: cast[int64](pool.uintegers[n.uintId]))
  of "u32":
    c.instr(I32Const, i32Const: cast[int32](pool.uintegers[n.uintId]))
  of "u16":
    c.instr(I32Const, i32Const: cast[int32](pool.uintegers[n.uintId]))
  of "u8":
    c.instr(I32Const, i32Const: cast[int32](pool.uintegers[n.uintId]))
  of "f64":
    c.instr(F64Const, f64Const: pool.floats[n.floatId])
  of "f32":
    c.instr(F32Const, f32Const: pool.floats[n.floatId])
  else:
    # TODO: f128?
    error c.m, "unsupported suffix", suffix

  c.genStoreDestination(dest)

proc genx(c: var GeneratedCode; n: var Cursor, dest: Destination) =
  let expr = n
  # echo &"genx {dest} {n}, {n.kind}, {n.exprKind}"
  # if n.exprKind != AddrC and n.kind != StringLit:
  #   c.flags.excl gfInCallImportC
  case n.exprKind
  of NoExpr:
    case n.kind
    of IntLit:
      c.instr(I64Const, i64Const: pool.integers[n.intId].int64)
      c.genStoreDestination(dest)
      inc n
    of UIntLit:
      c.instr(I64Const, i64Const: pool.uintegers[n.uintId].int64)
      c.genStoreDestination(dest)
      inc n
    of FloatLit:
      c.instr(F64Const, f64Const: pool.floats[n.floatId].float64) # todo: float64
      c.genStoreDestination(dest)
      inc n
    of CharLit:
      let ch = n.charLit
      c.instr(I32Const, i32Const: ch.int32)
      c.genStoreDestination(dest)
      inc n
    # of StringLit:
    #   if gfInCallImportC notin c.flags:
    #     c.add "(NC8*)"
    #   c.add makeCString(pool.strings[n.litId])
    #   inc n
    else:
      genLvalue c, n, dest
  of FalseC:
    c.instr(I32Const, i32Const: 0)
    c.genStoreDestination(dest)
    skip n
  of TrueC:
    c.instr(I32Const, i32Const: 1)
    c.genStoreDestination(dest)
    skip n
  of NilC:
    c.instr(I32Const, i32Const: 0)
    c.genStoreDestination(dest)
    skip n
  # of InfC:
  #   c.add "INF"
  #   skip n
  # of NegInfC:
  #   c.add "-INF"
  #   skip n
  # of NanC:
  #   c.add "NAN"
  #   skip n
  # of AconstrC:
  #   inc n
  #   let isUncheckedArray = n.typeKind in {PtrT, AptrT, FlexarrayT}
  #   c.objConstrType(n)
  #   c.add CurlyLe
  #   if not isUncheckedArray:
  #     c.add ".a = "
  #     c.add CurlyLe
  #   var i = 0
  #   while n.kind != ParRi:
  #     if i > 0: c.add Comma
  #     c.genx n
  #     inc i
  #   if not isUncheckedArray:
  #     c.add CurlyRi
  #   c.add CurlyRi
  #   skipParRi n
  # of OconstrC:
  #   inc n
  #   c.objConstrType(n)
  #   c.add CurlyLe
  #   var i = 0
  #   while n.kind != ParRi:
  #     if i > 0: c.add Comma
  #     if n.substructureKind == KvU:
  #       inc n
  #       c.add Dot
  #       var depth = n
  #       skip depth
  #       skip depth
  #       if depth.kind != ParRi:
  #         # inheritance depth
  #         assert depth.kind == IntLit
  #         let d = pool.integers[depth.intId]
  #         for _ in 0 ..< d:
  #           c.add "Q"
  #           c.add Dot
  #       c.genx n
  #       c.add AsgnOpr
  #       c.genx n
  #       if n.kind != ParRi: skip n
  #       skipParRi n
  #     elif n.exprKind == OconstrC:
  #       # inheritance
  #       c.add Dot
  #       c.add "Q"
  #       c.add AsgnOpr
  #       c.genx n
  #     else:
  #       c.genx n
  #     inc i
  #   c.add CurlyRi
  #   skipParRi n
  # of BaseobjC:
  #   inc n
  #   skip n # type not interesting for us
  #   var counter = pool.integers[n.intId]
  #   skip n
  #   c.genx n
  #   while counter > 0:
  #     c.add ".Q"
  #     dec counter
  #   skipParRi n
  # of ParC:
  #   c.add ParLe
  #   inc n
  #   genx c, n
  #   c.add ParRi
  #   skipParRi n
  # of AddrC:
  #   genAddr c, n
  #   c.flags.excl gfInCallImportC
  # of SizeofC:
  #   c.add "sizeof"
  #   c.add ParLe
  #   inc n
  #   genType c, n
  #   c.add ParRi
  #   skipParRi n
  # of AlignofC:
  #   c.add "NIM_ALIGNOF"
  #   c.add ParLe
  #   inc n
  #   genType c, n
  #   c.add ParRi
  #   skipParRi n
  # of OffsetofC:
  #   inc n
  #   c.add "offsetof"
  #   c.add ParLe
  #   genType c, n
  #   c.add Comma
  #   let name = mangle(pool.syms[n.symId])
  #   inc n
  #   c.add name
  #   c.add ParRi
  #   skipParRi n
  of CallC: genCall c, n, dest
  # of AddC: typedBinOp c, n, " + "
  # of SubC: typedBinOp c, n, " - "
  # of MulC: typedBinOp c, n, " * "
  # of DivC: typedBinOp c, n, " / "
  # of ModC: typedBinOp c, n, " % "
  # of ShlC: typedBinOp c, n, " << "
  # of ShrC: typedBinOp c, n, " >> "
  # of BitandC: typedBinOp c, n, " & "
  # of BitorC: typedBinOp c, n, " | "
  # of BitxorC: typedBinOp c, n, " ^ "
  # of BitnotC: typedUnOp c, n, " ~ "
  # of AndC: cmpOp c, n, " && "
  # of OrC: cmpOp c, n, " || "
  # of NotC: unOp c, n, "!"
  # of NegC: typedUnOp c, n, "-"
  # of EqC: cmpOp c, n, " == "
  # of NeqC: cmpOp c, n, " != "
  # of LeC: cmpOp c, n, " <= "
  # of LtC: cmpOp c, n, " < "
  # of CastC: typedUnOp c, n, ""
  of ConvC: genConv c, n, dest
  of SufC:
    inc n
    var value = n
    skip n
    let suffix = n
    skip n
    skipParRi n
    if value.kind == StringLit:
      genx c, value, dest
    else:
      genSuffixNumber c, value, suffix, dest
  # of ErrvC, AtC, DerefC, DotC, PatC, OvfC:
  #   genLvalue c, n
  else:
    error c.m, "genx: not implemented " & $n.exprKind & ", ", n

proc genToplevel(c: var GeneratedCode; n: var Cursor) =
  # ExternDecl ::= (imp ProcDecl | VarDecl | ConstDecl)
  # Include ::= (incl StringLiteral)
  # TopLevelConstruct ::= ExternDecl | ProcDecl | VarDecl | ConstDecl |
  #                       TypeDecl | Include | EmitStmt
  case n.stmtKind
  of ImpS:
    inc n
    discard takeProcDecl(n)
    skipParRi n
  # of InclS: genInclude c, n
  of ProcS: genProcDecl c, n, false
  # of VarS, GvarS, TvarS: genStmt c, n
  # of ConstS: genStmt c, n
  of DiscardS, AsgnS, KeepovfS, ScopeS, IfS,
      WhileS, CaseS, LabS, JmpS, TryS, RaiseS, CallS, OnErrS:
    # moveToInitSection:
    genStmt c, n, Destination(kind: Discard)
  # of TypeS:
  #   discard "handled in a different pass"
  #   skip n
  # of EmitS: genEmitStmt c, n
  # of StmtsS:
  #   inc n
  #   while n.kind != ParRi: genToplevel c, n
  #   skipParRi n
  else:
    # if n.pragmaKind == NodeclP:
    #   genNodecl c, n
    # else:
    #   error c.m, "expected top level construct but got: ", n
    error c.m, "expected top level construct but got: ", n

proc traverseCode(c: var GeneratedCode; n: var Cursor) =
  if n.stmtKind == StmtsS:
    inc n
    while n.kind != ParRi: genToplevel(c, n)
    # missing `inc n` here is intentional
  else:
    error c.m, "expected `stmts` but got: ", n

proc generateFunctionSignatures(c: var GeneratedCode; n: var Cursor) =
  if n.stmtKind == StmtsS:
    inc n
    while n.kind != ParRi:
      if n.stmtKind == ProcS:
        genProcSig c, n, false
      elif n.stmtKind == ImpS:
        genImp c, n
      else:
        inc n
  else:
    error c.m, "expected `stmts` but got: ", n

proc generateWasm*(inp, outp: string) =
  # registerTags()
  var c = initGeneratedCode(load(inp), 8)
  echo "generateWasm ", inp, " -> ", outp
  if inp.find("sys") != -1:
    return

  echo readFile(inp)
  # echo c.module

  c.builder = newWasmBuilder()
  c.builder.mems.add(WasmMem(typ: WasmMemoryType(limits: WasmLimits(min: 255))))
  c.builder.addExport("memory", 0.WasmMemIdx)
  c.functionRefTableIdx = c.builder.addTable()
  c.builder.addExport("__indirect_function_table", c.functionRefTableIdx)
  c.stackSize = wasmPageSize * 10
  c.activeDataOffset = align(c.stackSize, wasmPageSize)

  c.stackBase = c.builder.addGlobal(I32, mut=true, 0, id="__stack_base")
  c.stackEnd = c.builder.addGlobal(I32, mut=true, 0, id="__stack_end")
  c.stackPointer = c.builder.addGlobal(I32, mut=true, c.stackSize, id="__stack_pointer")
  c.memoryBase = c.builder.addGlobal(I32, mut=false, 0, id="__memory_base")
  c.tableBase = c.builder.addGlobal(I32, mut=false, 0, id="__table_base")
  c.heapBase = c.builder.addGlobal(I32, mut=false, 0, id="__heap_base")
  c.heapSize = c.builder.addGlobal(I32, mut=true, 0, id="__heap_size")

  var n = beginRead(c.m.src)
  generateFunctionSignatures c, n

  n = beginRead(c.m.src)
  traverseCode c, n

  let binary = c.builder.generateBinary()
  writeFile(outp, binary)
  let watOut = changeFileExt(outp, ".wat")
  writeFile(watOut, $c.builder)

  echo c.builder

  # var co = TypeOrder()
  # traverseTypes(c.m, co)

  # generateTypes(c, co)

  # var f = ""
  # f.add "(.nif24)\n(stmts"
  # f.add toString(c.data)
  # f.add toString(c.code)
  # f.add ")\n"

  # when defined(debug):
  #   echo f

  # if c.init.len > 0:
  #   quit "no init code implemented"
  # produceAsmCode f, outp

  echo "======================================= done"
