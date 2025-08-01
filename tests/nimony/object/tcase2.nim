import std/[syncio, assertions]

type
  TokenWithValue = object
    case kind: bool
    of true:
      value: string
    of false:
      indentation: int

proc sp(v: string): TokenWithValue =
  # test.nim(27, 17) Error: a case selecting discriminator 'kind' with value 'ltScalarPart' appears in the object construction, but the field(s) 'value' are in conflict with this value.
  TokenWithValue(value: v)

let a = sp("test")