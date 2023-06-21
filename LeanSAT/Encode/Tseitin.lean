import LeanSAT.Encode.EncCNF

namespace LeanSAT.Encode.Tseitin

open EncCNF

inductive Formula
| lit (l : Literal)
| not (f : Formula)
| and (fs : List Formula)
| or  (fs : List Formula)
deriving Repr, Inhabited

namespace Formula

def toString : Formula → String
| .lit l  => ToString.toString l
| .not f  => "¬" ++ toString f
| .and fs => "(" ++ (fs.subtypeSize.map (fun ⟨f,_⟩ => toString f) |> String.intercalate " ∧ ") ++ ")"
| .or fs  => "(" ++ (fs.subtypeSize.map (fun ⟨f,_⟩ => toString f) |> String.intercalate " ∨ ") ++ ")"
termination_by _ f => f
decreasing_by simp_wf; simp [Nat.add_comm 1]; try (apply Nat.le_step; assumption)

instance : ToString Formula := ⟨toString⟩

@[simp] def height : Formula → Nat
| .lit _ => 0
| .not f => height f + 1
| .and fs =>  fs.subtypeSize.map (fun ⟨f,h⟩ =>
      have := Nat.le_trans h (Nat.le_add_left _ 1)
      height f
    ) |>.maximum?.getD 0
| .or fs  =>  fs.subtypeSize.map (fun ⟨f,h⟩ =>
      have := Nat.le_trans h (Nat.le_add_left _ 1)
      height f
    ) |>.maximum?.getD 0
termination_by _ f => f

inductive NegNorm
| lit (l : Literal)
| and (fs : List NegNorm)
| or (fs : List NegNorm)

/-- logically equivalent to `.and fs` node,
    but absorbs any `and` nodes in `fs` -/
def NegNorm.and' (fs : List NegNorm) : NegNorm :=
  match aux fs with
  | [f'] => f'
  | fs' => .and fs'
where aux fs :=
  fs.subtypeSize.bind (fun
    | ⟨.and fs', h⟩ =>
      have : sizeOf fs' < sizeOf fs := by
        simp [Nat.add_comm 1] at h; apply Nat.le_of_lt h
      aux fs'
    | ⟨f,_⟩ => [f])
termination_by aux fs => sizeOf fs

/-- logically equivalent to `.or fs` node,
    but absorbs any `or` nodes in `fs` -/
def NegNorm.or' (fs : List NegNorm) : NegNorm :=
  match aux fs with
  | [f'] => f'
  | fs' => .or fs'
where aux fs :=
  fs.subtypeSize.bind (fun
    | ⟨.or fs', h⟩ =>
      have : sizeOf fs' < sizeOf fs := by
        simp [Nat.add_comm 1] at h; apply Nat.le_of_lt h
      aux fs'
    | ⟨f,_⟩ => [f])
termination_by aux fs => sizeOf fs

/-- negation normal form of formula `f`. also compresses nested and/ors
  where possible (so all children of each and should be ors). -/
def toNegNorm (f : Formula) : NegNorm :=
  match f with
  | .not (.not f) => toNegNorm f
  | .lit l        => .lit l
  | .not (.lit l) => .lit l.not
  | .and fs =>
      .and' (fs.subtypeSize.map (fun ⟨f,_h⟩ =>
        toNegNorm f
      ))
  | .not (.and fs) =>
      .or' (fs.subtypeSize.map (fun ⟨f,_h⟩ =>
        toNegNorm (.not f)
      ))
  | .or fs =>
      .or' (fs.subtypeSize.map (fun ⟨f,_h⟩ =>
        toNegNorm f
      ))
  | .not (.or fs) =>
      .and' (fs.subtypeSize.map (fun ⟨f,_h⟩ =>
        toNegNorm (.not f)
      ))
termination_by _ f => sizeOf f + match f with | .not _ => 1 | _ => 0
decreasing_by
  simp_wf; try split
  all_goals {
    simp [Nat.add_comm 1, Nat.lt_succ, Nat.succ_le_succ_iff] at *
    first
    | apply Nat.le_add_right
    | assumption
    | apply Nat.le_of_lt; assumption
  }

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
  let f := f.toNegNorm
  toplevel f
where
toplevel : Formula.NegNorm → EncCNF Unit
  | .lit l => addClause l
  | .and fs => newCtx "and." do
    for (i,⟨f,h⟩) in fs.subtypeSize.enum do
      have := Nat.le_trans h (Nat.le_add_left _ 1)
      newCtx s!"[{i}]." <| toplevel f
  | .or fs => newCtx "or." do
    let ls ← fs.enum.mapM (fun (i,f) => newCtx s!"[{i}]." <| aux f)
    addClause ls
aux : Formula.NegNorm → EncCNF Literal
  | .lit l => pure l
  | .and fs => newCtx "and." do
    let ls : List Literal ← fs.subtypeSize.enum.mapM (fun (i, ⟨f,h⟩) =>
      have := Nat.le_trans h (Nat.le_add_left _ 1)
      newCtx s!"[{i}]." <| aux f)
    let t ← mkTemp
    -- t ↔ ⋀ ls
    for l in ls do
      addClause (¬ t ∨ l)
    addClause (ls.map (·.not) ∨ t)
    return t
  | .or  fs => newCtx "or." do
    let ls ← fs.subtypeSize.enum.mapM (fun (i, ⟨f,h⟩) =>
      have := Nat.le_trans h (Nat.le_add_left _ 1)
      newCtx s!"[{i}]." <| aux f)
    let t ← mkTemp
    -- t ↔ ⋁ ls
    addClause (¬ t ∨ ls)
    for l in ls do
      addClause (¬l ∨ t)
    return t
termination_by
  toplevel f => f
  aux f => f

end Tseitin
