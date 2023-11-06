import LeanSAT

open LeanSAT Encode

namespace Examples.Yajilin

inductive Dir | up | down | left | right
deriving DecidableEq, Inhabited

structure Board where
  height : Nat
  width : Nat
  board : Fin height → Fin width → Option (Dir × Nat)
deriving Inhabited

structure BoardVars extends Board where
  pathLengthBits : Nat
  isNumber : Fin height → Fin width → IVar
  isFilled : Fin height → Fin width → IVar
  isInPath : Fin height → Fin width → IVar
  /-- `vertLine i j` iff there is a connection between `(i,j)` and `(i+1,j)` -/
  vertLine : Fin height.pred → Fin width → IVar
  /-- `horzLine i j` iff there is a connection between `(i,j)` and `(i,j+1)` -/
  horzLine : Fin height → Fin width.pred → IVar
  /-- whether `(i,j)` is lex-before the first path cell -/
  isLTRoot : Fin height → Fin width → IVar
  /-- whether `(i,j)` is connected to the root in `n` steps -/
  rootDist : Fin height → Fin width → BinNumber pathLengthBits
deriving Inhabited

open EncCNF Tseitin

def mkVars (b : Board) : EncCNF BoardVars := do
  /- the farthest a path can be to the root is ⌊b.height * b.width / 2⌋,
    so we want ⌈log₂ (⌊b.height * b.width / 2⌋ + 2)⌉ bits to count 1 past
    the max without overflowing -/
  let pathLengthBits := (b.height * b.width / 2 + 1).log2 + 1
  let isNumber ← mkVarBlock "isNumber" [b.height, b.width]
  let isFilled ← mkVarBlock "isFilled" [b.height, b.width]
  let isInPath ← mkVarBlock "isInPath" [b.height, b.width]
  let vertLine ← mkVarBlock "vertLine" [b.height.pred, b.width]
  let horzLine ← mkVarBlock "horzLine" [b.height, b.width.pred]
  let isLTRoot ← mkVarBlock "isLTRoot" [b.height, b.width]
  let rootDist ← mkVarBlock "rootDist" [b.height, b.width, pathLengthBits]
  return { b with
    pathLengthBits
    isNumber := (isNumber[·][·])
    isFilled := (isFilled[·][·])
    isInPath := (isInPath[·][·])
    vertLine := (vertLine[·][·])
    horzLine := (horzLine[·][·])
    isLTRoot := (isLTRoot[·][·])
    rootDist := (rootDist[·][·])
  }

/-- each neighbor square & the line var that goes to it -/
def neighbors (b : BoardVars) (i : Fin b.height) (j : Fin b.width) : Array (Fin b.height × Fin b.width × IVar) := Id.run do
  let mut res : Array _ := #[]
  for i' in i.predCast do
    res := res.push (⟨i', Nat.lt_of_lt_of_le i'.isLt (Nat.pred_le _)⟩, j, b.vertLine i' j)
  for i' in i.castPred' do
    res := res.push (cast (congrArg Fin <| Nat.succ_pred (· ▸ i |>.elim0)) i'.succ, j, b.vertLine i' j)
  for j' in j.predCast do
    res := res.push (i, ⟨j', Nat.lt_of_lt_of_le j'.isLt (Nat.pred_le _)⟩, b.horzLine i j')
  for j' in j.castPred' do
    res := res.push (i, cast (congrArg Fin <| Nat.succ_pred (· ▸ j |>.elim0)) j'.succ, b.horzLine i j')
  return res

def fillVarsInDir (b : BoardVars) (i : Fin b.height) (j : Fin b.width) (d : Dir) : Array ILit :=
  match d with
  | .up => Array.ofFn (n := i) (fun n =>
      have : n < b.height := Nat.lt_trans n.isLt i.isLt
      b.isFilled ⟨n, this⟩ j)
  | .down=> Array.ofFn (n := b.height-1-i) (fun n =>
      have : b.height-1-n < b.height := by
        calc
          _ = b.height-(n+1) := by rw [Nat.sub_sub, Nat.add_comm]
          _ < b.height := Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) (Nat.succ_le_succ (Nat.zero_le _))
      b.isFilled ⟨b.height-1-n, this⟩ j)
  | .left   => Array.ofFn (n := j) (fun n =>
      have : n < b.width := Nat.lt_trans n.isLt j.isLt
      b.isFilled i ⟨n, this⟩)
  | .right => Array.ofFn (n := b.width-1-j) (fun n =>
      have : b.width-1-n < b.width := by
        calc
          _ = b.width-(n+1) := by rw [Nat.sub_sub, Nat.add_comm]
          _ < b.width := Nat.sub_lt (Nat.zero_lt_of_lt j.isLt) (Nat.succ_le_succ (Nat.zero_le _))
      b.isFilled i ⟨b.width-1-n, this⟩)

open Model.PropForm.Notation in
def encode (b : Board) : EncCNF BoardVars := do
  let b ← mkVars b

  let pathLengthCap : BinNumber b.pathLengthBits ←
    mkVarBlock "pathLengthCap" [_]

  tseitin <| BinNumber.eqConst pathLengthCap <| b.height * b.width / 2 + 1

  for i in List.fins b.height do
    for j in List.fins b.width do
      /- isNumber, isFilled, isInPath partition all squares -/
      equalK #[b.isNumber i j, b.isFilled i j, b.isInPath i j] 1

      /- encode number squares -/
      match b.board i j with
      | some (d,n) =>
        addClause #[ b.isNumber i j ]
        /- there should be `n` filled squares in direction d -/
        equalK (fillVarsInDir b i j d) n
      | none =>
        addClause #[ -b.isNumber i j ]

      /- if a square is filled, its neighbors can't be.
        since this clause is symmetric up/down and left/right.
        we only add the clause down or right. -/
      for i' in i.succ? do
        addClause #[ -b.isFilled i j, -b.isFilled i' j ]
      for j' in j.succ? do
        addClause #[ -b.isFilled i j, -b.isFilled i j' ]

      /- if a square is not in path, it can't have any lines connected -/
      assuming #[ -b.isInPath i j ]
        <| equalK (neighbors b i j |>.map (·.2.2)) 0

      /- if a square is in path, it should have 2 lines connected -/
      assuming #[ b.isInPath i j ]
        <| equalK (neighbors b i j |>.map (·.2.2)) 2

      /- now we constrain the root of the path -/

      let lexPrev :=
        match i.pred?, j.pred? with
        | _, some j' => some (i,j')
        | some i', _ => some (i',j)
        | none, none => none

      match lexPrev with
      | none =>
        tseitin (b.isLTRoot i j ↔ ¬ b.isInPath i j)
      | some (i',j') =>
        tseitin (b.isLTRoot i j ↔ b.isLTRoot i' j' ∧ ¬ b.isInPath i j)

      /- then we constrain rootDist -/

      have : 0 < _ := Nat.mul_pos (Nat.zero_lt_of_lt i.isLt) (Nat.zero_lt_of_lt j.isLt)
      have : OfNat (Fin (b.height * b.width)) 0 := ⟨⟨0, this⟩⟩

      /- rootDist[i][j] < pathLengthCap -/
      tseitin <| ← (b.rootDist i j).lt pathLengthCap

      let isRoot :=
        match lexPrev with
        | none => ¬ b.isLTRoot i j
        | some (i',j') => ¬ b.isLTRoot i j ∧ b.isLTRoot i' j'

      /- if (i,j) is root, then rootDist[i][j] = 0 -/
      tseitin <| isRoot → BinNumber.eqConst (b.rootDist i j) 0

      /- otherwise, for some neighbor (i',j'),
            the path connects (i,j) <-> (i',j')
            AND rootDist[i][j] = rootDist[i'][j'] + 1 -/
      tseitin <| ¬ isRoot ∧ b.isInPath i j →
          (.disj'
            (← neighbors b i j
            |>.mapM (fun (i',j',v) => do
              return v ∧ (← BinNumber.eqSucc (b.rootDist i j) (b.rootDist i' j')))
            ).toList)

  return b

def printAssn (vars : BoardVars) (assn : HashAssn ILit) : String := Id.run do
  let mut s := s!"{vars.height}x{vars.width}\n"
  for i in List.fins vars.height do
    for j in List.fins vars.width do
      match vars.board i j with
      | some (d, n) =>
        s := s ++ (if n < 10 then toString n else "*")
               ++ (match d with
                    | .left => "←"
                    | .right => "→"
                    | .up => "↑"
                    | .down => "↓")
      | none =>
      if assn.find! (vars.isFilled i j) then
        s := s ++ "██"
      else
        match i.predCast.bind (assn.find? <| vars.vertLine · j)
            , i.castPred'.bind (assn.find? <| vars.vertLine · j)
            , j.predCast.bind (assn.find? <| vars.horzLine i ·)
            , j.castPred'.bind (assn.find? <| vars.horzLine i ·) with
        | some true, _, some true, _ =>
          s := s ++ "─┘"
        | some true, _, _, some true =>
          s := s ++ " └"
        | _, some true, some true, _ =>
          s := s ++ "─┐"
        | _, some true, _, some true =>
          s := s ++ " ┌"
        | some true, some true, _, _ =>
          s := s ++ " │"
        | _, _, some true, some true =>
          s := s ++ "──"
        | up, down, left, right =>
          panic! s!"assignment nonsense for {i},{j}: {up}, {down}, {left}, {right}"
    s := s.push '\n'
  return s

def solve [Solver IO] (b : Board) : IO Unit := do
  let (v,enc) := EncCNF.new! (encode b)
  match ←Solver.solve enc.toFormula with
  | .error => IO.println "error"
  | .unsat => IO.println "unsat"
  | .sat assn =>
    IO.println (printAssn v assn)

def parse (height width : Nat) (s : String) : Except String Board := do
  let lines := s.splitOn "\n"
  let pieces := List.toArray <| ← lines.mapM (fun line => do
    if h : line.length = 2*width then do
      return List.toArray <| ← List.fins width |>.mapM (fun i => do
        have : 2*i.val < line.length := sorry
        have : 2*i.val+1 < line.length := sorry
        match line[2*i.val], line[2*i.val+1] with
          | ' ', ' ' => return none
          | d  , 'U' => return some (.up   , d.toString.toNat!)
          | d  , 'D' => return some (.down , d.toString.toNat!)
          | d  , 'L' => return some (.left , d.toString.toNat!)
          | d  , 'R' => return some (.right, d.toString.toNat!)
          | a  , b   => throw s!"got the 2 characters {a}{b}"
      )
    else
      throw s!"line length {2*width} expected but received length {line.length}"
  )

  return { height, width, board := fun i j => pieces[i]![j]! }

def smallBoard : Except String Board :=
  parse 4 4 <|
    "      0D" ++ "\n" ++
    "  0L    " ++ "\n" ++
    "  1R    " ++ "\n" ++
    "        "

def bigBoard : Except String Board :=
  parse 32 32 <|
    "                    1L                    1R            0R      " ++ "\n" ++
    "                    1L              4R    3R                    " ++ "\n" ++
    "                                                                " ++ "\n" ++
    "  1L  2U    1U      0U                    4R                    " ++ "\n" ++
    "                0L  1L          2U        1U                  4D" ++ "\n" ++
    "              3L    7R                    1U                    " ++ "\n" ++
    "                    0U3R                  0R        2U2U  0R    " ++ "\n" ++
    "            2L  3L                              5L              " ++ "\n" ++
    "                    2R                    3D                    " ++ "\n" ++
    "                    4R    2U              3D                    " ++ "\n" ++
    "0D3U1U  1U  1L1D1U1L  2U2L2U  2L2L1U  2L1D  2U2D  5D3U3U3U0R  3U" ++ "\n" ++
    "                    3L                    3R                    " ++ "\n" ++
    "                    1L  1D                2R                    " ++ "\n" ++
    "      5D                                  0R                    " ++ "\n" ++
    "  5D                3L                4R  2D              1U  3U" ++ "\n" ++
    "                    2L                3L  1R                    " ++ "\n" ++
    "                    1L                                          " ++ "\n" ++
    "0D              6R  2D      4D            2R              2U    " ++ "\n" ++
    "            5U                                                  " ++ "\n" ++
    "                    2D    3R        5U    1R                    " ++ "\n" ++
    "                    2D                    3R                    " ++ "\n" ++
    "  0L2D0L0D3U5U  1L1L  2L1D  3D5U5U  1D2D1D  2R2R4D1D  4D1R1R1R  " ++ "\n" ++
    "                    5R                    2R                    " ++ "\n" ++
    "3R                  0R                                          " ++ "\n" ++
    "                    3R                    3R          3D        " ++ "\n" ++
    "                0L                        1R                    " ++ "\n" ++
    "            3L      1D                                          " ++ "\n" ++
    "                    1D                    5L            0R      " ++ "\n" ++
    "                    2L                    2L              4U    " ++ "\n" ++
    "  0D  0L            1D                    0L                    " ++ "\n" ++
    "                                    0D    1R              1R    " ++ "\n" ++
    "                    3L                    0R      0R            "

def bigBoard2 : Except String Board :=
  parse 17 17 <|
    "2D2R                              \n" ++
    "              3R                  \n" ++
    "            3R                    \n" ++
    "        3D                        \n" ++
    "              2D      3L          \n" ++
    "          4R          2R          \n" ++
    "  4R      3R                      \n" ++
    "  5R      4R          2R          \n" ++
    "                                  \n" ++
    "4R                                \n" ++
    "    4R      3R      2R            \n" ++
    "    4R      3R      2R            \n" ++
    "                                  \n" ++
    "          3R                      \n" ++
    "  5R      4R          2R          \n" ++
    "  3R      2R          1R          \n" ++
    "                                  "

def main [Solver IO] := do
  --solve (← IO.ofExcept smallBoard)
  solve (← IO.ofExcept bigBoard)
