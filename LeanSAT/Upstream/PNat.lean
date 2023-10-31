import Mathlib.Data.PNat.Defs

instance : HAdd PNat Nat PNat where
  hAdd | ⟨a,h⟩, b => ⟨a+b, Nat.add_pos_left h _⟩
