import LeanSAT.Encode.EncCNF

namespace LeanSAT.Encode.Tseitin

open EncCNF

inductive Formula
| lit (l : Literal)
| not (f : Formula)
| and (fs : List Formula)
| or  (fs : List Formula)
deriving Repr

namespace Formula

def height : Formula → Nat
| .lit _ => 0
| .not f => 1 + height f
| .and fs =>  fs.subtypeSize.map (fun ⟨f,h⟩ =>
      have := Nat.le_trans h (Nat.le_add_left _ 1)
      height f
    ) |>.maximum?.getD 0
| .or fs  =>  fs.subtypeSize.map (fun ⟨f,h⟩ =>
      have := Nat.le_trans h (Nat.le_add_left _ 1)
      height f
    ) |>.maximum?.getD 0
termination_by _ f => f

def normSize (f : Formula) :=
  f.height + match f with | .not _ => 1 | _ => 0

def normalize : Formula → Formula
| .lit l => .lit l
| .not (.lit l) => .lit l.not
| .not (.not f) =>
  have : normSize f < normSize (.not (.not f)) := by simp [normSize, height]; split <;> sorry
  normalize f
| .not (.and fs) =>
  let f' := .or <| fs.map .not
  have : normSize f' < normSize (.not (.and fs)) := by simp [normSize, height]; sorry
  normalize f'
| .not (.or fs) =>
  let f' := .and <| fs.map .not
  have : normSize f' < normSize (.not (.or fs)) := sorry
  normalize f'
| .and fs =>
  let fs' := fs.subtypeSize.bind (fun ⟨f,h⟩ =>
    have : normSize f < normSize (.and fs) := sorry
    match normalize f with
    | .and fs => fs
    | f => [f]
  )
  match fs' with
  | [] => .and []
  | [f] => f
  | fs => .and fs
| .or fs =>
  let fs' := fs.subtypeSize.bind (fun ⟨f,h⟩ =>
    have : normSize f < normSize (.or fs) := sorry
    match normalize f with
    | .or fs => fs
    | f => [f]
  )
  match fs' with
  | [] => .or []
  | [f] => f
  | fs => .or fs
termination_by _ f => normSize f

def implies (hyp con : Formula) : Formula := .or [hyp.not, con]
def iff (a b : Formula) : Formula := .and [.implies a b, .implies b a]
def false : Formula := .or []
def true : Formula := .and []

end Formula

namespace Notation
scoped instance : Coe Literal Formula := ⟨.lit⟩
scoped instance : OfNat Formula n := ⟨OfNat.ofNat (α := Literal) n⟩
scoped notation:max "¬" a:40 => Formula.not a
scoped notation:35 a:36 " ∧ " b:35 => Formula.and [a, b]
scoped notation:30 a:31 " ∨ " b:30 => Formula.or [a,b]
scoped notation:25 a:26 " → " b:25 => Formula.implies a b
scoped notation:20 a:21 " ↔ " b:21 => Formula.iff a b
end Notation

open LeanSAT.Notation in
def tseitin (f : Formula) : EncCNF Unit :=
  let f := f.normalize
  match f with
  | .not _ => panic! s!"shouldn't have any nots after normalization; found {repr f}"
  | .lit l => addClause l
  | .and fs => do
    let ls ← fs.mapM aux
    for l in ls do
      addClause l
  | .or fs => do
    let ls ← fs.mapM aux
    addClause ls
where aux : Formula → EncCNF Literal
| .not _ => panic! s!"shouldn't have any nots after normalization; found {repr f}"
| .lit l => pure l
| .and fs => do
  let ls : List Literal ← fs.subtypeSize.mapM (fun ⟨f,h⟩ =>
    have := Nat.le_trans h (Nat.le_add_left _ 1)
    aux f)
  let t ← mkTemp
  -- t ↔ ⋀ ls
  for l in ls do
    addClause (¬ t ∨ l)
  addClause (ls.map (·.not) ∨ t)
  return t
| .or  fs => do
  let ls ← fs.subtypeSize.mapM (fun ⟨f,h⟩ =>
    have := Nat.le_trans h (Nat.le_add_left _ 1)
    aux f)
  let t ← mkTemp
  -- t ↔ ⋁ ls
  addClause (¬ t ∨ ls)
  for l in ls do
    addClause (¬l ∨ t)
  return t
termination_by aux f => f

end Tseitin
