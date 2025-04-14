


import Init.Data.UInt.Basic

namespace UInt8

def minVal : UInt8 := 0
def maxVal : UInt8 := ⟨UInt8.size - 1, by rw [size]; omega⟩

def asciiZero : UInt8 := 48
def asciiOne : UInt8 := 49
def asciiTwo : UInt8 := 50
def asciiNine : UInt8 := 57
def asciiNeg : UInt8 := 45
def EOF : UInt8 := maxVal

@[inline, always_inline]
def isDigit (c : UInt8) : Bool :=
  (asciiZero <= c && c <= asciiNine) || (c = 100)

@[inline, always_inline]
def isDigit' (c : UInt8) : UInt8 :=
  if (asciiZero <= c && c <= asciiNine) || (c = 100) then 1
  else 0

@[inline, always_inline]
def isSpace (c : UInt8) : Bool :=
  (9 <= c && c <= 13)  /- '\t', '\n', '\v', '\f', '\r' -/
  || c == 32           /- ' ' -/

@[inline, always_inline]
def isSpace' (c : UInt8) : UInt8 :=
  if (9 <= c && c <= 13)  /- '\t', '\n', '\v', '\f', '\r' -/
     || c == 32           /- ' ' -/
  then 1
  else 0

@[inline, always_inline]
def digitToNat (c : UInt8) : Nat :=
  (c - asciiZero).toNat

@[inline, always_inline]
def digitToUInt32 (c : UInt8) : UInt32 :=
  (c - asciiZero).toUInt32

end UInt8

namespace UInt32

def minVal : UInt32 := 0
def maxVal : UInt32 := ⟨UInt32.size - 1, by rw [size]; omega⟩
def EOF : UInt32 := maxVal

def asciiZero : UInt32 := 48
def asciiOne : UInt32 := 49
def asciiTwo : UInt32 := 50
def asciiNine : UInt32 := 57
def asciiNeg : UInt32 := 45

@[inline, always_inline]
def isDigit (c : UInt32) : Bool :=
  asciiZero <= c && c <= asciiNine

@[inline, always_inline]
def isSpace (c : UInt32) : Bool :=
  (9 <= c && c <= 13)  /- '\t', '\n', '\v', '\f', '\r' -/
  || c == 32           /- ' ' -/

@[inline, always_inline]
def digitToNat (c : UInt32) : Nat :=
  (c - asciiZero).toNat

@[inline, always_inline]
def digitToUInt32 (c : UInt32) : UInt32 :=
  (c - asciiZero)

end UInt32

export UInt32 (EOF)


namespace USize

protected theorem succ_le_of_lt {a b : USize} : a < b → a + 1 ≤ b := by
  simp [USize.lt_def, USize.le_def, Fin.lt_def, Fin.le_def]
  intro h
  stop
  have h_lt₁ := Nat.le_of_lt h
  have h_le := Nat.succ_le_of_lt h
  have : (a + 1).val ≤ b.val := by sorry
  simp only [USize.lt_def, Fin.lt]
  done

theorem toNat_add_one_of_lt {a b : USize} : a < b → (a + 1).toNat = a.toNat + 1 := by
  sorry
  done

protected theorem sub_succ_lt_self {a b : USize} : a < b → b - (a + 1) < b - a := by
  -- sub_val_of_le
  intro h
  have h_lt₁ := Nat.le_of_lt h
  have h_le := Nat.succ_le_of_lt h
  have : (a + 1).val ≤ b.val := by sorry
  simp only [USize.sub_def, USize.lt_def, Fin.lt_def]
  stop
  rw [Fin.sub_val_of_le h_lt₁]
  rw [Fin.sub_val_of_le this]
  stop
  done

end USize
