

# proc foo(a: int32, b: int16, c: int8, d: int64, e: bool, f: char, g: float, h: float32) =
#   var a: int32 = int32.default
#   var b: int16 = int16.default
#   var c: int8 = int8.default
#   var d: int64 = int64.default
#   var e: bool = bool.default
#   var f: char = 'a'
#   var g: float = float.default
#   var h: float32 = float32.default

proc bar(): int =
  result = 123

proc testNoParams() {.importc: "my:host/test-interface\\test-no-params".}
# proc uiae2(a: int32, b: int64, c: float32, d: float64) {.importc: "xvlc".}

proc foo(a: int64): int64 =
  result = a

proc start() {.exportc.} =
  # echo "hello"
  # let a = 5
  # let b = foo(5)
  # let c = a
  # uiae(123)
  # uiae2(420, 69, 123.456.float32, 987.654)
  discard foo(5)

  testNoParams()
