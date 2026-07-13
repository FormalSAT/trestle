
import Experiments.SR.Data.UInt.Defs
import Std.Tactic.BVDecide

namespace UInt8

theorem ne_neg_of_isDigit {c : UInt8} : c.isDigit → c ≠ Char.toUInt8 '-' := by
  rintro h rfl
  contradiction

theorem not_isSpace_of_isDigit {c : UInt8} : c.isDigit → ¬c.isSpace := by
  simp [isDigit, isSpace, Char.toUInt8]
  bv_decide

theorem not_isDigit_of_isSpace {c : UInt8} : c.isSpace → ¬c.isDigit := by
  simp [isDigit, isSpace, Char.toUInt8]
  bv_decide

theorem isSpace_of_isNewline {c : UInt8} : c.isNewline → c.isSpace := by
  simp [isNewline, isSpace, Char.toUInt8]
  rintro rfl
  simp

@[simp]
theorem neg_not_isDigit : ¬(Char.toUInt8 '-').isDigit := by
  simp [isDigit, Char.toUInt8]

@[simp]
theorem neg_not_isSpace : ¬(Char.toUInt8 '-').isSpace := by
  simp [isSpace, Char.toUInt8]

end UInt8

namespace USize

/- A fixed-width integer is less than its successor if it is less than any other fixed-width integer. -/
theorem lt_succ_of_lt {i j : USize} : i < j → i < i + 1 := by
  intro hij
  rw [USize.lt_iff_toNat_lt] at hij ⊢
  have : j.toNat < USize.size := by exact toNat_lt_two_pow_numBits j
  have : ¬(USize.size ≤ i.toNat + 1) := by omega
  simp [Nat.add_mod_eq_ite, this]

theorem le_of_le_of_lt {i j k : USize} : i ≤ j → j < k → i ≤ k :=
  fun hij hjk => USize.le_of_lt <| USize.lt_of_le_of_lt hij hjk

theorem le_of_lt_of_le {i j k : USize} : i < j → j ≤ k → i ≤ k :=
  fun hij hjk => USize.le_of_lt <| USize.lt_of_lt_of_le hij hjk

theorem toNat_lt_of_lt_toUSize {i : USize} {n : Nat} : i < n.toUSize → i.toNat < n := by
  intro hi
  have hi' : i.toNat < n % (2 ^ System.Platform.numBits) := by
    simpa [USize.lt_iff_toNat_lt] using hi
  exact Nat.lt_of_lt_of_le hi' (Nat.mod_le _ _)

theorem sub_lt_sub_of_lt_of_le {a b c : USize}
    : a < b → b ≤ c → c - b < c - a := by
  simp [USize.lt_iff_toNat_lt, USize.le_iff_toNat_le]
  intro hab hbc
  simp [USize.toNat_sub_of_le _ _ hbc, USize.toNat_sub_of_le _ _ (USize.le_of_lt_of_le hab hbc)]
  omega

theorem sub_le_sub_of_le_of_le {a b c : USize}
    : a ≤ b → b ≤ c → c - b ≤ c - a := by
  simp [USize.le_iff_toNat_le]
  intro hab hbc
  simp [USize.toNat_sub_of_le _ _ hbc, USize.toNat_sub_of_le _ _ (USize.le_trans hab hbc)]
  rw [← Nat.sub_add_comm (Nat.le_trans hab hbc), Nat.add_sub_assoc hab]
  apply Nat.le_add_right

protected theorem succ_le_of_lt {a b : USize} : a < b → a + 1 ≤ b := by
  simp [USize.lt_iff_toNat_lt, USize.le_iff_toNat_le, Nat.add_mod_eq_ite]
  intro h
  have : b.toNat < USize.size := toNat_lt_two_pow_numBits b
  simp [size] at this
  replace : ¬(2 ^ System.Platform.numBits ≤ a.toNat + 1) := by omega
  simp [this]
  exact Nat.succ_le_of_lt h

theorem sub_succ_lt_sub_of_lt {a b : USize}
    : a < b → b - (a + 1) < b - a :=
  fun hab => sub_lt_sub_of_lt_of_le (USize.lt_succ_of_lt hab) (USize.succ_le_of_lt hab)

end USize /- namespace -/
