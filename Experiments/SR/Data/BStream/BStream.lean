/-

Author: Cayden Codel
Carnegie Mellon University

-/

import Lean
import Experiments.SR.Data.UInt.Basic

structure BStream where
  stream : IO.FS.Stream
  buffer : ByteArray
  bufferSize : USize
  iter : USize

abbrev BStreamM := StateT BStream IO

namespace BStream

def ofStream (s : IO.FS.Stream) (bufferSize : USize := 2048) : BStream := {
  stream := s,
  buffer := ByteArray.empty,
  bufferSize := bufferSize,
  iter := 0
}

def ofHandle (h : IO.FS.Handle) (bufferSize : USize := 1024) : BStream :=
  ofStream (IO.FS.Stream.ofHandle h) bufferSize

def ofFilePath (filePath : System.FilePath) (bufferSize : USize := 1024) : IO BStream := do
  let h ← IO.FS.Handle.mk filePath .read
  return ofHandle h bufferSize

def peek : BStreamM UInt32
  | ⟨stream, buffer, bufferSize, iter⟩ => do
    if iter < buffer.usize then
      return (buffer[iter]!.toUInt32, ⟨stream, buffer, bufferSize, iter⟩)
    else
      let buffer ← stream.read bufferSize
      if buffer.size = 0 then
        return ⟨EOF, ⟨stream, buffer, bufferSize, 0⟩⟩
      else
        return ⟨buffer[0]!.toUInt32, ⟨stream, buffer, bufferSize, 0⟩⟩

def getc : BStreamM UInt32
  | ⟨stream, buffer, bufferSize, iter⟩ => do
    if iter < buffer.usize then
      let ch := buffer[iter]!
      return (ch.toUInt32, { stream := stream, buffer := buffer, bufferSize := bufferSize, iter := iter + 1 })
    else
      let buffer ← stream.read bufferSize
      if buffer.size = 0 then
        return (EOF, { stream := stream, buffer := buffer, bufferSize := bufferSize, iter := 0 })
      else
        let ch := buffer[0]!
        return (ch.toUInt32, { stream := stream, buffer := buffer, bufferSize := bufferSize, iter := 1 })

def getc! : BStreamM UInt8
  | ⟨stream, buffer, bufferSize, iter⟩ => do
    if iter < buffer.usize then
      let ch := buffer[iter]!
      return (ch, { stream := stream, buffer := buffer, bufferSize := bufferSize, iter := iter + 1 })
    else
      let buffer ← stream.read bufferSize
      if buffer.size = 0 then
        panic! "getc!: unexpected EOF"
      else
        let ch := buffer[0]!
        return (ch, { stream := stream, buffer := buffer, bufferSize := bufferSize, iter := 1 })

def ungetc (_ch : UInt8) : BStreamM Unit
  | ⟨stream, buffer, bufferSize, iter⟩ => do
    if iter > 0 then
      return ((), { stream := stream, buffer := buffer, bufferSize := bufferSize, iter := iter - 1 })
    else
      return ((), { stream := stream, buffer := buffer, bufferSize := bufferSize, iter := 0 })

/--
  Consumes all whitespace characters until a non-whitespace character is encountered.
  The non-whitespace character is left in the stream for subsequent reading.
-/
partial def ws : BStreamM Unit := do
  let ch ← getc
  if ch.isSpace then
    ws
  else if ch = EOF then
    return ()
  else
    ungetc ch.toUInt8

/-- Reads up to and including the next newline character, or until EOF. -/
partial def line : BStreamM Unit := do
  let ch ← getc
  if ch = EOF || ch.isNewline then
    return ()
  else
    line

private partial def readNatDigits (acc : Nat) : BStreamM Nat := do
  let ch ← getc
  if ch = EOF then
    return acc
  else
    let ch8 := ch.toUInt8
    if ch8.isDigit then
      readNatDigits (acc * 10 + ch8.digitToNat)
    else
      ungetc ch8
      return acc

private partial def readUInt32Digits (acc : UInt32) : BStreamM UInt32 := do
  let ch ← getc
  if ch = EOF then
    return acc
  else
    let ch8 := ch.toUInt8
    if ch8.isDigit then
      readUInt32Digits (acc * 10 + ch8.digitToUInt32)
    else
      ungetc ch8
      return acc

private partial def readUInt64Digits (acc : UInt64) : BStreamM UInt64 := do
  let ch ← getc
  if ch = EOF then
    return acc
  else
    let ch8 := ch.toUInt8
    if ch8.isDigit then
      readUInt64Digits (acc * 10 + ch8.digitToUInt64)
    else
      ungetc ch8
      return acc

def readNat : BStreamM Nat := do
  ws
  let ch ← getc
  if ch = EOF then
    return 0
  else
    let ch8 := ch.toUInt8
    if ch8.isDigit then
      readNatDigits ch8.digitToNat
    else
      ungetc ch8
      return 0

def readNat! : BStreamM Nat := do
  ws
  let ch ← getc
  if ch = EOF then
    panic! "readNat!: unexpected EOF before encountering any digits"
  else
    let ch8 := ch.toUInt8
    if ch8.isDigit then
      readNatDigits ch8.digitToNat
    else
      ungetc ch8
      panic! s!"readNat!: unexpected character before encountering any digits: {Char.ofNat ch.toNat}"

def readInt : BStreamM Int := do
  ws
  let ch ← getc
  if ch = EOF then
    return 0
  else
    let ch8 := ch.toUInt8
    if ch8 = Char.toUInt8 '-' then
      let n ← readNat
      return -n
    else if ch8.isDigit then
      ungetc ch8
      let n ← readNat
      return n
    else
      ungetc ch8
      return 0

def readInt! : BStreamM Int := do
  ws
  let ch ← getc
  if ch = EOF then
    panic! "readInt!: unexpected EOF"
  else
    let ch8 := ch.toUInt8
    if ch8 = Char.toUInt8 '-' then
      let n ← readNat!
      return -n
    else if ch8.isDigit then
      ungetc ch8
      let n ← readNat!
      return n
    else
      ungetc ch8
      panic! s!"readInt!: unexpected character before encountering any digits: {Char.ofNat ch.toNat}"

def readUInt32NoWs : BStreamM UInt32 := do
  let ch ← getc
  if ch = EOF then
    panic! "readUInt32NoWs: unexpected EOF before encountering any digits"
  else
    let ch8 := ch.toUInt8
    if ch8.isDigit then
      readUInt32Digits ch8.digitToUInt32
    else
      ungetc ch8
      panic! s!"readUInt32NoWs: unexpected character before encountering any digits: {Char.ofNat ch.toNat}"

def readUInt32 : BStreamM UInt32 := do
  ws
  readUInt32NoWs

def readUInt32! : BStreamM UInt32 := do
  ws
  readUInt32NoWs

def readInt32NoWs : BStreamM Int := do
  let ch ← getc
  if ch = EOF then
    panic! "readInt32NoWs: unexpected EOF before encountering any digits"
  else
    let ch8 := ch.toUInt8
    if ch8 = Char.toUInt8 '-' then
      let n ← readUInt32NoWs
      return -(Int.ofNat n.toNat)
    else if ch8.isDigit then
      ungetc ch8
      let n ← readUInt32NoWs
      return Int.ofNat n.toNat
    else
      ungetc ch8
      panic! s!"readInt32NoWs: unexpected character before encountering any digits: {Char.ofNat ch.toNat}"

def readInt32 : BStreamM Int := do
  ws
  readInt32NoWs

def readInt32! : BStreamM Int := do
  ws
  readInt32NoWs

def readUInt64NoWs : BStreamM UInt64 := do
  let ch ← getc
  if ch = EOF then
    panic! "readUInt64NoWs: unexpected EOF before encountering any digits"
  else
    let ch8 := ch.toUInt8
    if ch8.isDigit then
      readUInt64Digits ch8.digitToUInt64
    else
      ungetc ch8
      panic! s!"readUInt64NoWs: unexpected character before encountering any digits: {Char.ofNat ch.toNat}"

def readUInt64 : BStreamM UInt64 := do
  ws
  readUInt64NoWs

def readUInt64! : BStreamM UInt64 := do
  ws
  readUInt64NoWs

def readInt64NoWs : BStreamM Int := do
  let ch ← getc
  if ch = EOF then
    panic! "readInt64NoWs: unexpected EOF before encountering any digits"
  else
    let ch8 := ch.toUInt8
    if ch8 = Char.toUInt8 '-' then
      let n ← readUInt64NoWs
      return -(Int.ofNat n.toNat)
    else if ch8.isDigit then
      ungetc ch8
      let n ← readUInt64NoWs
      return Int.ofNat n.toNat
    else
      ungetc ch8
      panic! s!"readInt64NoWs: unexpected character before encountering any digits: {Char.ofNat ch.toNat}"

def readInt64 : BStreamM Int := do
  ws
  readInt64NoWs

def readInt64! : BStreamM Int := do
  ws
  readInt64NoWs

/-- Scans the stream to match a format string. Similar to `fscanf()`. -/
def scanMatch (formatStr : String) : BStreamM Bool := do
  let rec loop : List Char → BStreamM Bool
    | [] => return true
    | ch :: rest => do
        if ch.toUInt8.isSpace then
          ws
          loop rest
        else
          let ch' ← getc
          if ch' = EOF then
            return false
          else if ch.toUInt8 = ch'.toUInt8 then
            loop rest
          else
            return false
  loop formatStr.toList

end BStream
