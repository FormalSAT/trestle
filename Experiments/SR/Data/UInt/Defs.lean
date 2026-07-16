
import Init.Data.UInt.Basic

namespace UInt8

def maxVal : UInt8 := ⟨UInt8.size - 1, by rw [size]; omega⟩

abbrev EOF : UInt8 := maxVal

@[extern "uint8_is_digit"]
def isDigit (c : UInt8) : Bool :=
     c == (Char.toUInt8 '0')
  || c == (Char.toUInt8 '1')
  || c == (Char.toUInt8 '2')
  || c == (Char.toUInt8 '3')
  || c == (Char.toUInt8 '4')
  || c == (Char.toUInt8 '5')
  || c == (Char.toUInt8 '6')
  || c == (Char.toUInt8 '7')
  || c == (Char.toUInt8 '8')
  || c == (Char.toUInt8 '9')

theorem ne_EOF_of_isDigit {c : UInt8} : isDigit c → c ≠ EOF := by
  simp [isDigit]
  rintro h rfl
  contradiction

@[extern "uint8_is_space"]
def isSpace (c : UInt8) : Bool :=
     c == (Char.toUInt8 ' ')
  || c == (Char.toUInt8 '\t')
  || c == (Char.toUInt8 '\n')
  || c == 11         -- '\v'
  || c == 12         -- '\f'
  || c == (Char.toUInt8 '\r')

theorem ne_EOF_of_isSpace {c : UInt8} : isSpace c → c ≠ EOF := by
  simp [isSpace]
  rintro h rfl
  contradiction

@[inline, always_inline]
def isNewline (c : UInt8) : Bool :=
  c == (Char.toUInt8 '\n')

/--
  Converts an ASCII digit character to its numeric value.
  If `c` is not an ASCII digit, the result is unspecified.

  The designers of the ASCII codes were clever: the characters 0-9 start at
  decimal value 48, which has binary 0b00001100. This means that if we mask
  by 15 (0b11110000), we can get the numbers directly.
-/
@[inline, always_inline]
private def asciiDigitToDigit (c : UInt8) : UInt8 :=
  c &&& 15    -- 0b1111

@[inline, always_inline]
def digitToNat (c : UInt8) : Nat :=
  (asciiDigitToDigit c).toNat

@[inline, always_inline]
def digitToInt (c : UInt8) : Int :=
  Int.ofNat <| c.digitToNat

@[inline, always_inline]
def digitToUSize (c : UInt8) : USize :=
  UInt8.toUSize <| asciiDigitToDigit c

@[inline, always_inline]
def digitToUInt16 (c : UInt8) : UInt16 :=
  UInt8.toUInt16 <| asciiDigitToDigit c

@[inline, always_inline]
def digitToUInt32 (c : UInt8) : UInt32 :=
  UInt8.toUInt32 <| asciiDigitToDigit c

@[inline, always_inline]
def digitToUInt64 (c : UInt8) : UInt64 :=
  UInt8.toUInt64 <| asciiDigitToDigit c

end UInt8

namespace UInt32

def maxVal : UInt32 := ⟨UInt32.size - 1, by rw [size]; omega⟩
def EOF : UInt32 := maxVal

@[extern "uint32_is_digit"]
def isDigit (c : UInt32) : Bool :=
     c == (UInt8.toUInt32 <| Char.toUInt8 '0')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '1')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '2')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '3')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '4')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '5')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '6')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '7')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '8')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '9')

@[extern "uint32_is_space"]
def isSpace (c : UInt32) : Bool :=
     c == (UInt8.toUInt32 <| Char.toUInt8 ' ')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '\t')
  || c == (UInt8.toUInt32 <| Char.toUInt8 '\n')
  || c == 11                           -- '\v'
  || c == 12                           -- '\f'
  || c == (UInt8.toUInt32 <| Char.toUInt8 '\r')

@[inline, always_inline]
def isNewline (c : UInt32) : Bool :=
  c == (UInt8.toUInt32 <| Char.toUInt8 '\n')

def numDigits (x : UInt32) : UInt32 :=
  if x < 10 then 1
  else if x < 100 then 2
  else if x < 1000 then 3
  else if x < 10000 then 4
  else if x < 100000 then 5
  else if x < 1000000 then 6
  else if x < 10000000 then 7
  else if x < 100000000 then 8
  else if x < 1000000000 then 9
  else 10

end UInt32 /- namespace -/

export UInt32 (EOF)

namespace UInt64

def numDigits (x : UInt64) : UInt64 :=
  if x < 10 then 1
  else if x < 100 then 2
  else if x < 1000 then 3
  else if x < 10000 then 4
  else if x < 100000 then 5
  else if x < 1000000 then 6
  else if x < 10000000 then 7
  else if x < 100000000 then 8
  else if x < 1000000000 then 9
  else if x < 10000000000 then 10
  else if x < 100000000000 then 11
  else if x < 1000000000000 then 12
  else if x < 10000000000000 then 13
  else if x < 100000000000000 then 14
  else if x < 1000000000000000 then 15
  else if x < 10000000000000000 then 16
  else if x < 100000000000000000 then 17
  else if x < 1000000000000000000 then 18
  else if x < 10000000000000000000 then 19
  else 20

end UInt64 /- namespace -/
