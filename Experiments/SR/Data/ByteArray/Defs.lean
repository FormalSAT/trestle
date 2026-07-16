/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Lean
import Experiments.SR.Data.UInt.Basic
import Experiments.SR.Data.UInt.Defs

/-!

A modification of `String.Iterator` on `ByteArray`s.
It assumes that the string, represented as a `ByteArray` is in ASCII format.

These functions are written with efficiency in mind.
In general, these functions take in `ByteArray` and an iterator `iter`,
but they only return an updated `iter`, since the array is not modified.
In addition, the iterator is a `USize` as opposed to a `Nat`,
since the length of the string (array) is assumed to fit in a `USize`.

-/

namespace ByteArray

/--
  Peeks at the character under the iterator.
  Returns `UInt8.EOF` if the iterator is out of bounds.
-/
def peek (arr : ByteArray) (iter : USize) : UInt8 :=
  if hi : iter < arr.usize then
    arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)
  else
    UInt8.EOF

/-- A Lean version of `getc` from C/C++. An alias for `peek`. -/
@[simp] abbrev getc := peek

/--
  Skips characters in `arr` meeting a predicate `pred`, starting from `iter`.
  On return, `iter` points to the first character that does NOT meet `pred`.

  If `iter` is out of bounds, `iter` is returned.
-/
@[specialize]
def skip (arr : ByteArray) (iter : USize) (pred : UInt8 → Bool) : USize :=
  if hi : iter < arr.usize then
    let ch := arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)
    if pred ch then
      skip arr (iter + 1) pred
    else
      iter
  else
    iter
termination_by arr.usize - iter
decreasing_by simp; apply USize.lt_iff_toNat_lt.mp; apply USize.sub_succ_lt_sub_of_lt; assumption

/--
  Moves the iterator forward until it points to the first non-whitespace character.
-/
@[extern "lean_byte_array_ws"]
def ws (arr : @& ByteArray) (iter : USize) : USize :=
  skip arr iter (·.isSpace)

/--
  Consumes a line until and including the first newline character `'\n'`.
  Returns the updated iterator, which either points to just after the newline
  character, or to the end of the array if no newline is found.
-/
@[extern "lean_byte_array_line"]
def line (arr : ByteArray) (iter : USize) : USize :=
  let iter := skip arr iter (! ·.isNewline)
  if iter < arr.usize then
    iter + 1
  else
    iter

/--
  Consumes the next token and any preceding whitespace.
  On return, `iter` points to the first whitespace character after the
  first contiguous sequence of non-whitespace characters,
  or to the end of the array.
-/
@[extern "lean_byte_array_token"]
def token (arr : ByteArray) (iter : USize) : USize :=
  let iter := ws arr iter
  skip arr iter (! ·.isSpace)

@[extern "lean_byte_array_skip_nat_no_ws"]
def skipNatNoWs (arr : @& ByteArray) (iter : USize) : USize :=
  skip arr iter (·.isDigit)

@[extern "lean_byte_array_skip_int_no_ws"]
def skipIntNoWs (arr : @& ByteArray) (iter : USize) : USize :=
  let ch := peek arr iter
  if ch = Char.toUInt8 '-' then
    skipNatNoWs arr (iter + 1)
  else
    skipNatNoWs arr iter

def skipNat (arr : ByteArray) (iter : USize) : USize :=
  let iter := ws arr iter
  skipNatNoWs arr iter

def skipInt (arr : ByteArray) (iter : USize) : USize :=
  let iter := ws arr iter
  skipIntNoWs arr iter

/-! # readNat and readInt -/

class ParseNumeric (α : Type u)
  extends Add α, Zero α where
  ofUInt8 : UInt8 → α
  mulTen : α → α
  toInt : α → Int
  toInt_zero : toInt (0 : α) = 0

attribute [simp] ParseNumeric.toInt_zero

instance (α : Type u) [ParseNumeric α] : Inhabited α where
  default := 0

@[simp] theorem ParseNumeric.default_eq_zero (α : Type u) [ParseNumeric α] : (default : α) = 0 := rfl

instance : ParseNumeric USize where
  ofUInt8 := UInt8.digitToUSize
  mulTen n := n * (10 : USize)
  toInt n := Int.ofNat n.toNat
  toInt_zero := rfl

instance : ParseNumeric UInt16 where
  ofUInt8 := UInt8.digitToUInt16
  mulTen n := n * (10 : UInt16)
  toInt n := Int.ofNat n.toNat
  toInt_zero := rfl

instance : ParseNumeric UInt32 where
  ofUInt8 := UInt8.digitToUInt32
  mulTen n := n * (10 : UInt32)
  toInt n := Int.ofNat n.toNat
  toInt_zero := rfl

instance : ParseNumeric UInt64 where
  ofUInt8 := UInt8.digitToUInt64
  mulTen n := n * (10 : UInt64)
  toInt n := Int.ofNat n.toNat
  toInt_zero := rfl

instance : ParseNumeric Nat where
  ofUInt8 := UInt8.digitToNat
  mulTen n := n * (10 : Nat)
  toInt n := Int.ofNat n
  toInt_zero := rfl

/--
  Reads a natural number from `arr` starting at `iter`. Parsing stops
  at the first non-digit character, or when the end of the array is reached.

  If the first character is not a digit, `0` is returned, and `iter` is unchanged.

  The `ParseNumeric` type enables different fixed-width representations
  to be parsed, which might be more efficient than `Nat`s.
-/
@[specialize]
def readNatNoWs {α : Type u} [ParseNumeric α] (arr : ByteArray) (iter : USize) (acc : α := 0) : α × USize :=
  if hi : iter < arr.usize then
    let ch := arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)
    if ch.isDigit then
      readNatNoWs arr (iter + 1) (ParseNumeric.mulTen acc + ParseNumeric.ofUInt8 ch)
    else
      (acc, iter)
  else
    (acc, iter)
termination_by arr.usize - iter
decreasing_by simp; apply USize.lt_iff_toNat_lt.mp; apply USize.sub_succ_lt_sub_of_lt; assumption

/--
  A wrapper for `readNatNoWs` that checks if the first character is a digit.
  If not, or if the iterator is out of bounds, the function panics.
-/
@[specialize]
def readNatNoWs! {α : Type u} [ParseNumeric α] (arr : ByteArray) (iter : USize) : α × USize :=
  if iter < arr.usize then
    let ch := peek arr iter
    if ch.isDigit then
      readNatNoWs arr iter 0
    else
      let n := panic! "Attempted to read a Nat, but the first character is not a digit: {Char.ofNat ch.toNat}"
      (n, iter)
  else
    let n := panic! "Attempted to read a Nat, but the iterator is out of bounds"
    (n, iter)

@[specialize, inline, always_inline]
def readNat {α : Type u} [ParseNumeric α] (arr : ByteArray) (iter : USize) : α × USize :=
  let iter := ws arr iter
  if iter < arr.usize then
    readNatNoWs arr iter 0
  else
    (0, iter)

@[specialize, inline, always_inline]
def readNat! {α : Type u} [ParseNumeric α] (arr : ByteArray) (iter : USize) : α × USize :=
  let iter := ws arr iter
  readNatNoWs! arr iter

/--
  Parses an integer using an internal accumulator type `α`.
  Using a fixed-width type such as `UInt32` will be more efficient.
-/
@[specialize]
def readInt (α : Type u) [ParseNumeric α] (arr : ByteArray) (iter : USize) : Int × USize :=
  let iter := ws arr iter
  let ch := peek arr iter
  if ch = Char.toUInt8 '-' then
    let (n, iter) := readNatNoWs (α := α) arr (iter + 1) 0
    (-(ParseNumeric.toInt n), iter)
  else if ch.isDigit then
    let (n, iter) := readNatNoWs (α := α) arr iter 0
    (ParseNumeric.toInt n, iter)
  else
    (0, iter)

/--
  A version of `readInt` that panics if the first character is not 0-9 or '-',
  or if the iterator is out of bounds.
-/
@[specialize]
def readInt! (α : Type u) [ParseNumeric α] (arr : ByteArray) (iter : USize) : Int × USize :=
  let iter := ws arr iter
  let ch := peek arr iter
  if ch = Char.toUInt8 '-' then
    let (n, iter) := readNatNoWs! (α := α) arr (iter + 1)
    (-(ParseNumeric.toInt n), iter)
  else if ch.isDigit then
    let (n, iter) := readNatNoWs! (α := α) arr iter
    (ParseNumeric.toInt n, iter)
  else if ch = UInt8.EOF then
    let n := panic! "Attempted to read an integer, but the iterator is out of bounds"
    (n, iter)
  else
    let n := panic! s!"Attempted to read an integer, but the first character is not a digit or '-': {Char.ofNat ch.toNat}"
    (n, iter)

/-! # readUInt variants -/

def readUInt32NoWs.loop (arr : ByteArray) (iter : USize) (acc : UInt32) : UInt32 :=
  if hi : iter < arr.usize then
    let ch := arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)
    if ch.isDigit then
      readUInt32NoWs.loop arr (iter + 1) (acc * 10 + UInt8.digitToUInt32 ch)
    else
      acc
  else
    acc
termination_by arr.usize - iter
decreasing_by simp; apply USize.lt_iff_toNat_lt.mp; apply USize.sub_succ_lt_sub_of_lt; assumption

/--
  Reads a 32-bit unsigned integer from `arr` starting at `iter`, but doesn't
  move the iterator.  Call `skipNat` after to move the iterator forward.
-/
@[extern "lean_byte_array_read_uint32_no_ws"]
def readUInt32NoWs (arr : @& ByteArray) (iter : USize) : UInt32 :=
  if iter < arr.usize then
    let ch := peek arr iter
    if ch.isDigit then
      readUInt32NoWs.loop arr iter 0
    else
      panic! s!"Attempted to read a UInt32, but the first character is not a digit: {Char.ofNat ch.toNat}"
  else
    panic! "Attempted to read a UInt32, but the iterator is out of bounds"

@[inline]
def readUInt32 (arr : ByteArray) (iter : USize) : UInt32 :=
  let iter := ws arr iter
  readUInt32NoWs arr iter

@[extern "lean_byte_array_read_int32_no_ws"]
def readInt32NoWs (arr : @& ByteArray) (iter : USize) : Int :=
  if iter < arr.usize then
    let ch := peek arr iter
    if ch = Char.toUInt8 '-' then
      (-(Int.ofNat <| UInt32.toNat <| readUInt32NoWs arr (iter + 1)))
    else
      Int.ofNat <| UInt32.toNat <| readUInt32NoWs arr iter
  else
    panic! "Attempted to read an Int32, but the iterator is out of bounds"

@[inline]
def readInt32 (arr : ByteArray) (iter : USize) : Int :=
  let iter := ws arr iter
  readInt32NoWs arr iter

def readUInt64NoWs.loop (arr : ByteArray) (iter : USize) (acc : UInt64) : UInt64 :=
  if hi : iter < arr.usize then
    let ch := arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)
    if ch.isDigit then
      readUInt64NoWs.loop arr (iter + 1) (acc * 10 + UInt8.digitToUInt64 ch)
    else
      acc
  else
    acc
termination_by arr.usize - iter
decreasing_by simp; apply USize.lt_iff_toNat_lt.mp; apply USize.sub_succ_lt_sub_of_lt; assumption

/--
  Reads a 64-bit unsigned integer from `arr` starting at `iter`, but doesn't
  move the iterator.  Call `skipNat` after to move the iterator forward.
-/
@[extern "lean_byte_array_read_uint64_no_ws"]
def readUInt64NoWs (arr : @& ByteArray) (iter : USize) : UInt64 :=
  if iter < arr.usize then
    let ch := peek arr iter
    if ch.isDigit then
      readUInt64NoWs.loop arr iter 0
    else
      panic! s!"Attempted to read a UInt64, but the first character is not a digit: {Char.ofNat ch.toNat}"
  else
    panic! "Attempted to read a UInt64, but the iterator is out of bounds"

@[inline]
def readUInt64 (arr : ByteArray) (iter : USize) : UInt64 :=
  let iter := ws arr iter
  readUInt64NoWs arr iter

@[extern "lean_byte_array_read_int64_no_ws"]
def readInt64NoWs (arr : @& ByteArray) (iter : USize) : Int :=
  if iter < arr.usize then
    let ch := peek arr iter
    if ch = Char.toUInt8 '-' then
      (-(Int.ofNat <| UInt64.toNat <| readUInt64NoWs arr (iter + 1)))
    else
      Int.ofNat <| UInt64.toNat <| readUInt64NoWs arr iter
  else
    panic! "Attempted to read an Int64, but the iterator is out of bounds"

@[inline]
def readInt64 (arr : ByteArray) (iter : USize) : Int :=
  let iter := ws arr iter
  readInt64NoWs arr iter

def undoBinaryMapping32 (x : UInt32) : Int :=
  if x &&& 1 = 1 then
    ((((x >>> 1).toNat) : Int) * -1)
  else
    (((x >>> 1).toNat) : Int)

def undoBinaryMapping64 (x : UInt64) : Int :=
  if x &&& 1 = 1 then
    ((((x >>> 1).toNat) : Int) * -1)
  else
    (((x >>> 1).toNat) : Int)

def readBinInt32Impl (arr : ByteArray) (iter : USize) (acc : UInt32 := 0) (shift : UInt32 := 0) : Int :=
  if hi : iter < arr.usize then
    let atom := arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)
    let acc' := acc ||| ((atom &&& 127).toUInt32 <<< shift)
    if atom &&& 128 != 0 then
      readBinInt32Impl arr (iter + 1) acc' (shift + 7)
    else
      undoBinaryMapping32 acc'
  else
    panic! "Attempted to read a binary Int32, but the iterator is out of bounds"
termination_by arr.usize - iter
decreasing_by simp; apply USize.lt_iff_toNat_lt.mp; apply USize.sub_succ_lt_sub_of_lt; assumption

@[extern "lean_byte_array_read_bin_int32"]
def readBinInt32 (arr : @& ByteArray) (iter : @& USize) : Int :=
  readBinInt32Impl arr iter 0 0

def readBinInt64Impl (arr : ByteArray) (iter : USize) (acc : UInt64 := 0) (shift : UInt64 := 0) : Int :=
  if hi : iter < arr.usize then
    let atom := arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)
    let acc' := acc ||| ((atom &&& 127).toUInt64 <<< shift)
    if atom &&& 128 != 0 then
      readBinInt64Impl arr (iter + 1) acc' (shift + 7)
    else
      undoBinaryMapping64 acc'
  else
    panic! "Attempted to read a binary Int64, but the iterator is out of bounds"
termination_by arr.usize - iter
decreasing_by simp; apply USize.lt_iff_toNat_lt.mp; apply USize.sub_succ_lt_sub_of_lt; assumption

@[extern "lean_byte_array_read_bin_int64"]
def readBinInt64 (arr : @& ByteArray) (iter : @& USize) : Int :=
  readBinInt64Impl arr iter 0 0

@[extern "lean_byte_array_skip_bin_int"]
def skipBinInt (arr : ByteArray) (iter : USize) : USize :=
  if hi : iter < arr.usize then
    let atom := arr.uget iter (USize.toNat_lt_of_lt_toUSize hi)
    if atom &&& 128 != 0 then
      skipBinInt arr (iter + 1)
    else
      iter + 1
  else
    iter
termination_by arr.usize - iter
decreasing_by simp; apply USize.lt_iff_toNat_lt.mp; apply USize.sub_succ_lt_sub_of_lt; assumption

end ByteArray /- namespace -/
