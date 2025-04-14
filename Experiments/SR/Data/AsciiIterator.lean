/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Experiments.SR.UInt

/-!

A modification of `String.Iterator` that assumes that the string is an ASCII.

These functions take in `ByteArray` and an iterator `iter`,
but only return an updated `iter`, since the array will not be modified.

Also assumes that the length of the string fits in a `USize`.
-/

abbrev ByteArray' := { arr : ByteArray // arr.size < USize.size }

namespace ByteArray

/-
@[inline, always_inline]
partial def readInt : BStream2M Int
  | stream, bufferSize, ⟨buffer, iter⟩ => do
    let ⟨buffer, iter⟩ ← ws2Internal stream bufferSize ⟨buffer, iter⟩
    if hi : iter < buffer.usize then
      let rec @[inline, always_inline] loop (buffer : ByteArray) (iter : USize) (acc : UInt32) : IO (UInt32 × BStream2) := do
        if hi' : iter < buffer.usize then
          let ch := buffer.uget iter (by sorry)
          if ch.isDigit' != 0 then
          -- acc * 10 === (acc << 3) + (acc << 1)
            loop buffer (iter + 1) (acc * 10 + ch.digitToUInt32)
          else
            return (acc, { buffer := buffer, iter := iter })
        else
          let buffer ← read stream bufferSize
          if buffer.usize = 0 then
            return (acc, { buffer := buffer, iter := 0 })
          else
            loop buffer 0 acc

      let ch := buffer.uget iter (by sorry)
      if ch = UInt8.asciiNeg then
        let (n, bs) ← loop buffer (iter + 1) 0
        return (-(Int.ofNat n.toNat), bs)
      else
        let (n, bs) ← loop buffer iter 0
        return (Int.ofNat n.toNat, bs)
    else
      return (0, { buffer := buffer, iter := 0 })
-/

/--
  Returns the index of the first non-whitespace character.
-/
--@[inline, always_inline]
def ws (arr : ByteArray') (iter : USize) : USize :=
  let ⟨arr, h_arr⟩ := arr
  let size := arr.size.toUSize
  let rec loop (iter : USize) : USize :=
    if hi : iter < size then
      have : (arr.size.toUSize - (iter + 1)).toNat < (arr.size.toUSize - iter).toNat := by
        simp [size] at hi
        have := USize.succ_le_of_lt hi
        rw [USize.toNat_sub_of_le _ _ this]
        rw [USize.toNat_sub_of_le _ _ (Fin.le_of_lt hi)]
        rw [USize.toNat_add_one_of_lt hi]
        exact Nat.sub_succ_lt_self arr.size.toUSize.toNat iter.toNat hi
      let ch := arr.uget iter (by rw [← USize.toNat_ofNat_of_lt h_arr]; simpa using hi)
      if ch.isSpace' != 0 then
        loop (iter + 1)
      else
        iter
    else
      iter
  termination_by arr.size.toUSize - iter

  loop iter

/--
  Returns the index of the first whitespace character after whitespace and a
  non-whitespace token.

  For example, " abc de" would return 4 (pointing between "c" and "d").
-/
--@[inline, always_inline]
def skip (arr : ByteArray') (iter : USize) : USize :=
  let iter := ws arr iter
  let ⟨arr, _⟩ := arr
  let size := arr.size.toUSize
  let rec loop (iter : USize) : USize :=
    if hi : iter < size then
      have : (arr.size.toUSize - (iter + 1)).toNat < (arr.size.toUSize - iter).toNat := by
        simp [size] at hi
        have := USize.succ_le_of_lt hi
        rw [USize.toNat_sub_of_le _ _ this]
        rw [USize.toNat_sub_of_le _ _ (Fin.le_of_lt hi)]
        rw [USize.toNat_add_one_of_lt hi]
        exact Nat.sub_succ_lt_self arr.size.toUSize.toNat iter.toNat hi

      let ch := arr.uget iter (by
        simp [size, USize.lt_iff_toNat_lt, Nat.mod_eq_of_lt, *] at hi; exact hi)
      -- If the character is not a space, keep going
      if ch.isSpace' = 0 then
        loop (iter + 1)
      else
        iter
    else
      iter
  termination_by arr.size.toUSize - iter

  loop iter

--@[inline, always_inline]
def readNat (arr : ByteArray') (iter : USize) : Nat × USize :=
  let iter := ws arr iter
  let ⟨arr, h_arr⟩ := arr
  let size := arr.size.toUSize
  let rec loop (iter : USize) (acc : Nat) : Nat × USize :=
    if hi : iter < size then
      have : (arr.size.toUSize - (iter + 1)).toNat < (arr.size.toUSize - iter).toNat := by
        simp [size] at hi
        have := USize.succ_le_of_lt hi
        rw [USize.toNat_sub_of_le _ _ this]
        rw [USize.toNat_sub_of_le _ _ (Fin.le_of_lt hi)]
        rw [USize.toNat_add_one_of_lt hi]
        exact Nat.sub_succ_lt_self arr.size.toUSize.toNat iter.toNat hi

      let ch := arr.uget iter (by
        rw [← USize.toNat_ofNat_of_lt h_arr]
        
        --rw [USize.val_eq_of_lt hs]
        stop
        done)

      if ch.isDigit' != 0 then
        loop (iter + 1) (acc * 10 + ch.digitToNat)
      else
        (acc, iter)
    else
      (acc, iter)
  termination_by arr.size.toUSize - iter

  let ⟨n, iter⟩ := loop iter 0
  (n, iter)

--@[inline, always_inline]
def readInt (arr : ByteArray') (iter : USize) : Int × USize :=
  let iter := ws arr iter
  let ⟨arr, h_arr⟩ := arr
  let size := arr.size.toUSize
  if hi : iter < size then
    let ch := arr.uget iter (by sorry)
    if ch = UInt8.asciiNeg then
      let (n, iter) := readNat ⟨arr, h_arr⟩ (iter + 1)
      (-(Int.ofNat n), iter)
    else
      let (n, iter) := readNat ⟨arr, h_arr⟩ iter
      (Int.ofNat n, iter)
  else
    ⟨0, iter⟩

/--
  Peeks at the character under the iterator.
  Returns `UInt8.EOF` if the iterator is out of bounds.
-/
--@[inline, always_inline]
def peekc (arr : ByteArray') (iter : USize) : UInt8 :=
  let ⟨arr, h_arr⟩ := arr
  let size := arr.size.toUSize
  if iter < size then
    arr.uget iter (by sorry)
  else
    UInt8.EOF

theorem ws_iter_gt {arr : ByteArray'} {iter} :
  iter < arr.val.size.toUSize → (ws arr iter) > iter := by sorry

theorem readNat_iter_gt {arr : ByteArray'} {iter} :
  iter < arr.val.size.toUSize → (readNat arr iter).2 > iter := by sorry

theorem readInt_iter_gt {arr : ByteArray'} {iter} :
  iter < arr.val.size.toUSize → (readInt arr iter).2 > iter := by sorry


end ByteArray
