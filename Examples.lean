import Examples.Akari
import Examples.NumberLink

def mains :=
  [ ("Akari", Akari.main)
  , ("NumberLink", NumberLink.main)
  ]

def main (args : List String) : IO UInt32 := do
  IO.println "Example:"
  for (i, name, _) in mains.enum do
    IO.println s!"({i}) {name}"
  IO.print "Select example: "
  let selection ← (←IO.getStdin).getLine
  let selection ← IO.ofExcept <|
    selection.trim.toNat?.expectSome fun () => s!"Expected a number, got {selection}"
  if _h : selection < mains.length then
    mains[selection].2
  
  return 0
