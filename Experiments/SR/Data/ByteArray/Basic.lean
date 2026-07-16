
import Lean
import Experiments.SR.Data.ByteArray.Defs

open Lean
open Lean.Elab
open Lean.Elab.Tactic

/-- A common sequence of tactics for proving termination of an iterator
    getting closer to the size of an array. Via `USize.sub_succ_lt_sub_of_lt`. -/
macro "sub_succ" : tactic => `(tactic| (
    simp
    apply USize.lt_iff_toNat_lt.mp
    apply USize.sub_succ_lt_sub_of_lt
    assumption
  ))

namespace ByteArray

/-! # peek -/

theorem iter_lt_of_peek_ne_EOF {arr : ByteArray} {iter : USize}
    : peek arr iter ≠ UInt8.EOF → iter < arr.size.toUSize := by
  unfold peek
  simp
  exact fun hi _ => hi

theorem peek_eq_of_ge_size {arr : ByteArray} {iter : USize}
    : iter ≥ arr.size.toUSize → peek arr iter = UInt8.EOF := by
  unfold peek
  simp
  intro h h_con
  exact absurd h (USize.not_le.mpr h_con)

@[simp]
theorem peek_eq_size (arr : ByteArray) : peek arr arr.size.toUSize = UInt8.EOF :=
  peek_eq_of_ge_size (USize.le_refl _)

/-! # skip -/

@[simp]
theorem iter_le_skip (arr : ByteArray) (iter : USize) (pred : UInt8 → Bool)
    : iter ≤ skip arr iter pred := by
  unfold skip
  simp
  split
  · rename_i hi
    split
    · have := iter_le_skip arr (iter + 1) pred
      apply USize.le_trans (USize.le_of_lt _) this
      exact USize.lt_succ_of_lt hi
    · apply Nat.le_refl
  · apply Nat.le_refl
termination_by arr.size.toUSize - iter
decreasing_by sub_succ

theorem iter_lt_skip_of_peek_ne_EOF_of_pred_true {arr : ByteArray} {iter : USize} {pred : UInt8 → Bool}
    : peek arr iter ≠ UInt8.EOF → pred (peek arr iter) → iter < skip arr iter pred := by
  unfold skip
  simp
  split
  <;> rename_i hi
  · intro h_peek h_pred
    simp [peek, hi] at h_pred
    simp [h_pred]
    apply USize.lt_of_lt_of_le <| USize.lt_succ_of_lt hi
    apply iter_le_skip
  · simp [peek_eq_of_ge_size (USize.not_lt.mp hi)]

theorem iter_lt_skip_of_pred_uget_true {arr : ByteArray} {iter : USize} {pred : UInt8 → Bool}
      {hi : iter < arr.size.toUSize}
    : pred (arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)) → iter < skip arr iter pred := by
  unfold skip
  simp [hi]
  intro hp
  simp [hp]
  apply USize.lt_of_lt_of_le <| USize.lt_succ_of_lt hi
  apply iter_le_skip

theorem skip_eq_of_peek_pred_false {arr : ByteArray} {iter : USize} {pred : UInt8 → Bool}
    : ¬pred (peek arr iter) → skip arr iter pred = iter := by
  unfold skip peek
  simp
  intro hp hi hp'
  simp [hi, hp'] at hp

theorem skip_eq_of_uget_pred_false {arr : ByteArray} {iter : USize} {pred : UInt8 → Bool}
    (hi : iter < arr.size.toUSize)
    : ¬pred (arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)) → skip arr iter pred = iter := by
  unfold skip
  simp [hi]
  intro hp hp'
  simp [hp'] at hp

theorem skip_eq_of_ge_size {arr : ByteArray} {iter : USize}
    : iter ≥ arr.size.toUSize → ∀ pred, skip arr iter pred = iter := by
  intro hi pred
  unfold skip
  simp [USize.not_lt.mpr hi]

@[simp]
theorem skip_eq_size (arr : ByteArray) (pred : UInt8 → Bool)
    : skip arr arr.size.toUSize pred = arr.size.toUSize := by
  apply skip_eq_of_ge_size
  exact USize.le_refl _

theorem skip_le_of_le {arr : ByteArray} {iter : USize}
    : iter ≤ arr.size.toUSize → ∀ pred, skip arr iter pred ≤ arr.size.toUSize := by
  intro hi pred
  rcases USize.lt_or_eq_of_le hi with (h | rfl)
  · unfold skip
    simp [h]
    split
    · exact skip_le_of_le (USize.succ_le_of_lt h) pred
    · exact hi
  · simp
termination_by arr.size.toUSize - iter
decreasing_by sub_succ

theorem le_skip_of_le {iter₁ iter₂ : USize}
    : iter₁ ≤ iter₂ → ∀ arr pred, iter₁ ≤ skip arr iter₂ pred := by
  intro hi arr pred
  apply USize.le_trans hi
  exact iter_le_skip arr iter₂ pred

-- @[simp]
-- theorem skip_skip (arr : ByteArray) (iter : USize) (pred : UInt8 → Bool)
--     : skip arr (skip arr iter pred) pred = skip arr iter pred := by
--   unfold skip
--   stop
--   simp
--   split
--   · rename_i hsi
--     split
--     · split
--       · split
--         ·
--           done
--         done
--       done
--     done
--   ·
--     done
--   done


/-! # ws -/

@[simp]
theorem iter_le_ws (arr : ByteArray) (iter : USize) : iter ≤ ws arr iter :=
  iter_le_skip arr iter _

theorem ws_eq_of_ge_size {arr : ByteArray} {iter : USize}
    : iter ≥ arr.size.toUSize → ws arr iter = iter := by
  unfold ws
  intro hi
  apply skip_eq_of_ge_size hi

@[simp]
theorem ws_eq_size (arr : ByteArray) : ws arr arr.size.toUSize = arr.size.toUSize :=
  ws_eq_of_ge_size (USize.le_refl _)

theorem ws_le_of_le {arr : ByteArray} {iter : USize}
    : iter ≤ arr.size.toUSize → ws arr iter ≤ arr.size.toUSize := by
  intro hi
  unfold ws
  apply skip_le_of_le hi

theorem ws_eq_of_peek_isDigit {arr : ByteArray} {iter : USize}
    : (peek arr iter).isDigit → ws arr iter = iter := by
  intro h
  unfold ws
  apply skip_eq_of_peek_pred_false
  exact UInt8.not_isSpace_of_isDigit h

theorem ws_eq_of_uget_isDigit {arr : ByteArray} {iter : USize} (hi : iter < arr.size.toUSize)
    : (arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)).isDigit → ws arr iter = iter := by
  intro h
  unfold ws
  apply skip_eq_of_uget_pred_false hi
  exact UInt8.not_isSpace_of_isDigit h

-- @[simp]
-- theorem ws_ws (arr : ByteArray) (iter : USize) : ws arr (ws arr iter) = ws arr iter :=
--   skip_skip arr iter _

/-! # line -/

@[simp]
theorem iter_le_line (arr : ByteArray) (iter : USize)
    : iter ≤ line arr iter := by
  unfold line
  simp
  split
  · rename_i hi
    apply USize.le_of_le_of_lt <| iter_le_skip arr iter (! ·.isNewline)
    apply USize.lt_succ_of_lt hi
  · simp

theorem line_le_of_le {arr : ByteArray} {iter : USize}
    : iter ≤ arr.size.toUSize → line arr iter ≤ arr.size.toUSize := by
  intro hi
  unfold line
  simp
  split
  · rename_i h
    apply USize.succ_le_of_lt h
  · apply skip_le_of_le hi

theorem line_eq_of_ge_size {arr : ByteArray} {iter : USize}
    : iter ≥ arr.size.toUSize → line arr iter = iter := by
  intro hi
  unfold line
  simp
  simp [skip_eq_of_ge_size hi, USize.not_lt.mpr hi]

@[simp]
theorem line_eq_size (arr : ByteArray) : line arr arr.size.toUSize = arr.size.toUSize :=
  line_eq_of_ge_size (USize.le_refl _)

theorem le_line_of_le (arr : ByteArray) {iter₁ iter₂ : USize}
    : iter₁ ≤ iter₂ → iter₁ ≤ line arr iter₂ := by
  intro hi
  simp [line]
  split
  · rename_i hs
    apply USize.le_trans <| le_skip_of_le hi arr (! ·.isNewline)
    apply USize.le_of_lt
    exact USize.lt_succ_of_lt hs
  · apply le_skip_of_le hi

/-! # token -/

@[simp]
theorem iter_le_token (arr : ByteArray) (iter : USize)
    : iter ≤ token arr iter := by
  unfold token
  simp
  apply USize.le_trans <| iter_le_ws arr iter
  apply iter_le_skip

theorem token_eq_of_ge_size {arr : ByteArray} {iter : USize}
    : iter ≥ arr.size.toUSize → token arr iter = iter := by
  intro hi
  unfold token
  simp [ws_eq_of_ge_size hi, skip_eq_of_ge_size hi]

@[simp]
theorem token_eq_size {arr : ByteArray} : token arr arr.size.toUSize = arr.size.toUSize :=
  token_eq_of_ge_size (USize.le_refl _)

theorem token_le_of_le {arr : ByteArray} {iter : USize}
    : iter ≤ arr.size.toUSize → token arr iter ≤ arr.size.toUSize := by
  intro hi
  unfold token
  simp
  apply skip_le_of_le
  exact ws_le_of_le hi

/-! # skipNat, skipInt -/

@[simp]
theorem skipNoWs_eq_size (arr : ByteArray)
    : skipNatNoWs arr arr.size.toUSize = arr.size.toUSize := by
  unfold skipNatNoWs; simp

theorem skipNatNoWs_le_of_le {arr : ByteArray} {iter : USize}
    : iter ≤ arr.size.toUSize → skipNatNoWs arr iter ≤ arr.size.toUSize :=
  fun hi => skip_le_of_le hi fun x => x.isDigit

@[simp]
theorem le_skipNatNoWs (arr : ByteArray) (iter : USize)
    : iter ≤ skipNatNoWs arr iter := by
  unfold skipNatNoWs; simp

theorem iter_lt_skipNatNoWs_of_peek_isDigit {arr : ByteArray} {iter : USize}
    : UInt8.isDigit (peek arr iter) → iter < skipNatNoWs arr iter := by
  intro h_peek
  apply iter_lt_skip_of_peek_ne_EOF_of_pred_true _ h_peek
  apply UInt8.ne_EOF_of_isDigit h_peek

-- theorem skipInt_le_of_le {arr : ByteArray} {iter : USize}
--     : iter ≤ arr.size.toUSize → skipInt arr iter ≤ arr.size.toUSize := by
--   stop
--   intro hi
--   unfold skipInt
--   simp
--   split
--   · rename_i h_neg
--     apply skip_le_of_le hi fun x => x.isDigit || x == UInt8._minus
--     simp [h_neg]
--   · apply skipNatNoWs_le_of_le hi

/-! # readNat, readInt -/

section readNat

variable {α : Type u} [ParseNumeric α]

@[simp]
theorem iter_le_readNatNoWs (arr : ByteArray) (iter : USize) (acc : α)
    : iter ≤ (readNatNoWs (α := α) arr iter acc).2 := by
  unfold readNatNoWs
  simp
  split
  · rename_i hi
    split
    · apply USize.le_of_lt_of_le <| USize.lt_succ_of_lt hi
      apply iter_le_readNatNoWs
    · exact USize.le_rfl
  · simp
termination_by arr.size.toUSize - iter
decreasing_by sub_succ

theorem iter_lt_readNatNoWs_of_ne_zero {arr : ByteArray} {iter : USize}
    : (readNatNoWs (α := α) arr iter).1 ≠ 0 → iter < (readNatNoWs (α := α) arr iter).2 := by
  unfold readNatNoWs
  by_cases hi : iter < arr.size.toUSize
  <;> simp [hi]
  · intro h
    split
    <;> rename_i h_uget
    <;> simp [h_uget] at h
    · apply USize.lt_of_lt_of_le <| USize.lt_succ_of_lt hi
      simp

theorem readNatNoWs_le_of_le {arr : ByteArray} {iter : USize}
    : iter ≤ arr.size.toUSize → ∀ acc, (readNatNoWs (α := α) arr iter acc).2 ≤ arr.size.toUSize := by
  intro hi acc
  unfold readNatNoWs
  simp
  split
  · rename_i hi_lt
    split
    · apply readNatNoWs_le_of_le
      exact USize.succ_le_of_lt hi_lt
    · exact hi
  · exact hi
termination_by arr.size.toUSize - iter
decreasing_by sub_succ

@[simp]
theorem iter_le_readNat (arr : ByteArray) (iter : USize)
    : iter ≤ (readNat (α := α) arr iter).2 := by
  unfold readNat
  simp
  split
  · apply USize.le_trans <| iter_le_ws arr iter
    apply iter_le_readNatNoWs
  · apply iter_le_ws

theorem iter_lt_readNat_of_ne_zero {arr : ByteArray} {iter : USize}
    : (readNat (α := α) arr iter).1 ≠ 0 → iter < (readNat (α := α) arr iter).2 := by
  unfold readNat
  simp
  split
  · rename_i h_ws
    intro h
    apply USize.lt_of_le_of_lt <| iter_le_ws arr iter
    exact iter_lt_readNatNoWs_of_ne_zero h
  · simp

@[simp]
theorem iter_le_readInt (arr : ByteArray) (iter : USize)
    : iter ≤ (readInt (α := α) arr iter).2 := by
  unfold readInt
  simp
  split
  · rename_i hp
    simp
    apply USize.le_trans <| iter_le_ws arr iter
    have : peek arr (ws arr iter) ≠ UInt8.EOF := by simp [hp]; trivial
    replace := iter_lt_of_peek_ne_EOF this
    apply USize.le_of_lt_of_le <| USize.lt_succ_of_lt this
    apply iter_le_readNatNoWs
  · split
    · apply USize.le_trans <| iter_le_ws arr iter
      apply iter_le_readNatNoWs
    · simp

theorem iter_lt_readInt_iter_of_ne_zero {arr : ByteArray} {iter : USize}
    : (readInt (α := α) arr iter).1 ≠ 0 → iter < (readInt (α := α) arr iter).2 := by
  unfold readInt
  simp
  split
  · rename_i hp
    simp
    intro h
    have : peek arr (ws arr iter) ≠ UInt8.EOF := by simp [hp]; trivial
    replace := iter_lt_of_peek_ne_EOF this
    apply USize.lt_of_le_of_lt <| iter_le_ws arr iter
    apply USize.lt_of_lt_of_le <| USize.lt_succ_of_lt this
    apply iter_le_readNatNoWs
  · split
    · simp
      intro h
      apply USize.lt_of_le_of_lt <| iter_le_ws arr iter
      apply iter_lt_readNatNoWs_of_ne_zero
      intro h_con
      simp [h_con] at h
    · simp

theorem iter_lt_skipNat_of_readUInt32NoWs.loop_ne_zero {arr : ByteArray} {iter : USize}
    : readUInt32NoWs.loop arr iter 0 ≠ 0 → iter < skipNat arr iter := by
  unfold readUInt32NoWs.loop skipNat skipNatNoWs
  simp
  intro hi hd h_nz
  rw [ws_eq_of_uget_isDigit hi hd]
  apply iter_lt_skip_of_pred_uget_true hd
  exact hi

theorem iter_lt_skipNat_of_readUInt32NoWs_ne_zero {arr : ByteArray} {iter : USize}
    : readUInt32NoWs arr iter ≠ 0 → iter < skipNat arr iter := by
  unfold readUInt32NoWs
  simp
  intro _ _
  apply iter_lt_skipNat_of_readUInt32NoWs.loop_ne_zero

-- theorem iter_lt_skipNat_of_readUInt32 {arr : ByteArray} {iter}
--     : readUInt32 arr iter ≠ 0 → iter < skipNat arr iter := by
--   unfold readUInt32 skipNat
--   simp
--   intro h
--   apply USize.lt_of_le_of_lt <| iter_le_ws arr iter
--   have := iter_lt_skipNat_of_readUInt32NoWs_ne_zero h
--   simp [skipNat] at this
--   exact this

-- theorem iter_lt_skipInt_of_readInt32NoWs {arr : ByteArray} {iter : USize}
--     : readInt32NoWs arr iter ≠ 0 → iter < skipInt arr iter := by
--   unfold readInt32NoWs skipInt
--   simp
--   intro hi h
--   stop
--   split at h
--   · simp at h
--     done
--   ·
--     done
--   rw [ws_eq_of_uget_isDigit hi h_neg]
--   apply iter_lt_skip_of_pred_uget_true h_neg
--   exact hi

-- theorem iter_lt_skipInt_of_readInt32 {arr : ByteArray} {iter}
--     : readInt32 arr iter ≠ 0 → iter < skipInt arr iter := by
--   unfold readInt32 skipInt
--   stop
--   simp
--   intro h
--   apply USize.lt_of_le_of_lt <| iter_le_ws arr iter
--   have := iter_lt_skipNat_of_readUInt32NoWs_ne_zero h
--   simp [skipInt, skipNat] at this
--   exact this


end readNat

#exit
@[simp]
private theorem iter_le_readNatNoWs_loop (arr : ByteArray) (iter : USize) (acc : α)
    : iter ≤ (readNatNoWs.loop arr iter acc).2 := by
  unfold readNatNoWs.loop
  simp
  split
  · rename_i hi
    split
    · apply USize.le_of_lt_of_le (USize.lt_succ_of_lt hi)
      apply iter_le_readNatNoWs_loop
    · split
      · apply USize.le_refl
      · exact USize.le_of_lt hi
  · exact Nat.le_refl _
termination_by arr.size.toUSize - iter
decreasing_by simp; apply USize.lt_iff_toNat_lt.mp; apply USize.sub_succ_lt_sub_of_lt; assumption

@[simp]
theorem iter_le_readNatNoWs (arr : ByteArray) (iter : USize)
    : iter ≤ (readNatNoWs (α := α) arr iter).2 := by
  unfold readNatNoWs; simp; split <;> simp

@[simp]
private theorem readNatNoWs_loop_eq (arr : ByteArray) (acc : α)
    : readNatNoWs.loop arr arr.size.toUSize acc = (acc, arr.size.toUSize) := by
  unfold readNatNoWs.loop; simp

@[simp]
theorem readNatNoWs_eq_size (arr : ByteArray)
    : readNatNoWs (α := α) arr arr.size.toUSize = (0, arr.size.toUSize) := by
  simp [readNatNoWs]

private theorem readNatNoWs_loop_le_of_le {arr : ByteArray} {iter : USize}
    : iter ≤ arr.size.toUSize → ∀ (acc : α), (readNatNoWs.loop arr iter acc).2 ≤ arr.size.toUSize := by
  intro hi acc
  rcases USize.lt_or_eq_of_le hi with (h | h)
  · unfold readNatNoWs.loop
    simp [h]
    split
    · apply readNatNoWs_loop_le_of_le (USize.succ_le_of_lt h)
    · split
      · exact hi
      · apply USize.le_refl
  · simp [h]
termination_by arr.size.toUSize - iter
decreasing_by
  simp
  apply USize.lt_iff_toNat_lt.mp
  apply USize.sub_lt_sub_of_lt_of_le
  apply USize.lt_succ_of_lt (by assumption)
  apply USize.succ_le_of_lt (by assumption)

theorem readNatNoWs_le_of_le {arr : ByteArray} {iter : USize}
    : iter ≤ arr.size.toUSize → (readNatNoWs (α := α) arr iter).2 ≤ arr.size.toUSize := by
  intro hi
  unfold readNatNoWs
  simp
  split
  · apply readNatNoWs_loop_le_of_le hi
  · exact hi

@[simp]
theorem iter_le_readNat (arr : ByteArray) (iter : USize)
    : iter ≤ (readNat (α := α) arr iter).2 := by
  unfold readNat
  simp
  have h₁ := iter_le_ws arr iter
  have h₂ := iter_le_readNatNoWs (α := α) arr (ws arr iter)
  exact USize.le_trans h₁ h₂

@[simp]
theorem readNat_loop_eq_size (arr : ByteArray)
    : readNat arr arr.size.toUSize = (0, arr.size.toUSize) := by
  simp [readNat]

theorem readNat_iter_le_of_le {arr : ByteArray} {iter : USize}
    : iter ≤ arr.size.toUSize → (readNat (α := α) arr iter).2 ≤ arr.size.toUSize := by
  intro hi
  simp [readNat]
  exact readNatNoWs_le_of_le <| ws_le_of_le hi

@[simp]
theorem iter_le_readInt_iter (arr : ByteArray) (iter : USize)
    : iter ≤ (readInt (α := α) arr iter).2 := by
  unfold readInt
  simp
  have h₁ := iter_le_ws arr iter
  split
  · rename_i hp
    have : peek arr (ws arr iter) ≠ UInt8.EOF := by simp [hp]
    replace := iter_lt_of_peek_ne_EOF this
    simp
    apply USize.le_trans h₁
    apply USize.le_trans (USize.le_of_lt (USize.lt_succ_of_lt this))
    apply iter_le_readNatNoWs
    done
  · simp
    apply USize.le_trans h₁
    apply iter_le_readNatNoWs

@[simp]
theorem readInt_eq_size (arr : ByteArray)
    : readInt (α := α) arr arr.size.toUSize = (0, arr.size.toUSize) := by
  simp [readInt]

theorem readInt_iter_le_of_le {arr : ByteArray} {iter : USize}
    : iter ≤ arr.size.toUSize → (readInt (α := α) arr iter).2 ≤ arr.size.toUSize := by
  intro hi
  simp [readInt]
  split
  <;> simp
  · rename_i hp
    have : peek arr (ws arr iter) ≠ UInt8.EOF := by simp [hp]
    replace := iter_lt_of_peek_ne_EOF this
    apply readNatNoWs_le_of_le
    exact USize.succ_le_of_lt this
  · exact readNatNoWs_le_of_le <| ws_le_of_le hi



theorem iter_lt_readNat_of_ne_zero {arr : ByteArray} {iter : USize}
    : (readNat (α := α) arr iter).1 ≠ 0 → iter < (readNat (α := α) arr iter).2 := by
  unfold readNat
  simp
  intro h
  apply USize.lt_of_le_of_lt <| iter_le_ws arr iter
  apply iter_lt_readNatNoWs_of_ne_zero
  exact h

theorem iter_lt_readInt_iter_of_ne_zero {arr : ByteArray} {iter : USize}
    : (readInt (α := α) arr iter).1 ≠ 0 → iter < (readInt (α := α) arr iter).2 := by
  unfold readInt
  simp
  split
  · rename_i hp
    have : peek arr (ws arr iter) ≠ UInt8.EOF := by simp [hp]
    replace := iter_lt_of_peek_ne_EOF this
    simp at this
    simp
    intro h
    apply USize.lt_of_le_of_lt (iter_le_ws arr iter)
    apply USize.lt_trans (USize.lt_succ_of_lt this)
    apply iter_lt_readNatNoWs_of_ne_zero
    intro h_con
    simp [h_con] at h
  · simp
    intro h
    apply USize.lt_of_le_of_lt <| iter_le_ws arr iter
    apply iter_lt_readNatNoWs_of_ne_zero
    intro h_con
    simp [h_con] at h

end readNat /- section -/

end ByteArray
