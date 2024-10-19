import LeanSudoku.Basic

set_option relaxedAutoImplicit false

-- def List.mfirst' {M : Type → Type v} [Monad M] {α : Type} [Inhabited α] (f : α → M Bool) : List α → M α
-- | [] => return default
-- | (a::as) => do
--   let r ← f a
--   if r then return a else List.mfirst' f as

-- def List.mfiltermap {M : Type u → Type v} [Monad M] {α : Type w} {β : Type u}
--   (f : α → M (Option β)) : List α → M (List β) := sorry

-- | [] := return []
-- | (x::xs) := do
--     y ← f x,
--     r ← list.mfiltermap xs,
--     match y with
--     | none := return r
--     | some z := return (z::r)
--     end

def Lean.LocalContext.toList (ctx : Lean.LocalContext) : List Lean.LocalDecl :=
  ctx.foldr List.cons []
namespace Tactic.Sudoku

open Lean Meta Elab Tactic
open scoped Qq

def getSudoku : MetaM Q(Sudoku) := do
  let lctx ← getLCtx
  let board? ← lctx.findDeclM? fun decl ↦ do
    let ⟨1, ~q(Sudoku), ~q($s)⟩ ← Qq.inferTypeQ decl.toExpr | return none
    return some s
  match board? with
  | some board => return board
  | none => throwError m!"could not find sudoku variable"

structure CellData where
  (row col val : Fin 9)
  (e : Expr) (re ce ve : Q(Fin 9))
  (hr hc hv : Expr)

instance : ToMessageData CellData where
  toMessageData | {row, col, val, e, ..} => m!"({e} : s.f ({row}, {col}) = {val})"

example : 1 = 1 := by ring

structure OuterPencilData where
  (row₀ col₀ row₁ col₁ val : Fin 9)
  (e : Expr)

structure InnerPencilData where
  (row col : Fin 9)
  (vals : List (Fin 9))
  (e : Expr)

structure BoardInfo where
  (cd : List CellData)
  (op : List OuterPencilData)
  (ip : List InnerPencilData)

-- instance : has_to_format cell_data

-- Evaluates an expression `e` of type `Fin 9` to a numeral
-- and then returns the result `n` along with an expression proving that
-- `e = ($(mkNatLit n) : Fin 9)`.
def evalFin (e : Q(Fin 9)) : MetaM (Option (Fin 9 × Expr)) := do
  let ⟨natLit, proof⟩ ← Mathlib.Meta.NormNum.deriveNat e (q(Fin.instAddMonoidWithOne 9))
  let some n ← getNatValue? natLit | return none
  return some ((n : Fin 9), proof)

def parseCellData (s : Q(Sudoku)) (e : Expr) : MetaM (Option CellData) := do
  let ⟨0, ~q(Sudoku.f $s' ($er, $ec) = $ev), e⟩ ← Qq.inferTypeQ e | return none
  -- TODO: add a check that `s = s'`? e.g.
  -- `guard (← isDefEq s s')`
  let some (r, hr) ← evalFin er | return none
  let some (c, hc) ← evalFin ec | return none
  let some (v, hv) ← evalFin ev | return none
  return some ⟨r, c, v, e, er, ec, ev, hr, hc, hv⟩

def parseOuterPencilData (s : Q(Sudoku)) (e : Expr) : MetaM (Option OuterPencilData) := do
  let ⟨0, ~q(Sudoku.snyder $s' $er₀ $ec₀ $er₁ $ec₁ $ev), e⟩ ← Qq.inferTypeQ e | return none
  -- TODO: add a check that `s = s'`?
  let some (r₀, _) ← evalFin er₀ | return none
  let some (c₀, _) ← evalFin ec₀ | return none
  let some (r₁, _) ← evalFin er₁ | return none
  let some (c₁, _) ← evalFin ec₁ | return none
  let some (v, _) ← evalFin ev | return none
  return some ⟨r₀, c₀, r₁, c₁, v, e⟩

def parseInnerPencilData₂ (s : Q(Sudoku)) (e : Expr) : MetaM (Option InnerPencilData) := do
  let ⟨0, ~q(Sudoku.double $s' $er $ec $ev₁ $ev₂), e⟩ ← Qq.inferTypeQ e | return none
  -- TODO: add a check that `s = s'`?
  let some (r, _) ← evalFin er | return none
  let some (c, _) ← evalFin ec | return none
  let some (v₁, _) ← evalFin ev₁ | return none
  let some (v₂, _) ← evalFin ev₂ | return none
  return some ⟨r, c, [v₁, v₂], e⟩

def parseInnerPencilData₃ (s : Q(Sudoku)) (e : Expr) : MetaM (Option InnerPencilData) := do
  let ⟨0, ~q(Sudoku.triple $s' $er $ec $ev₁ $ev₂ $ev₃), e⟩ ← Qq.inferTypeQ e | return none
  -- TODO: add a check that `s = s'`?
  let some (r, _) ← evalFin er | return none
  let some (c, _) ← evalFin ec | return none
  let some (v₁, _) ← evalFin ev₁ | return none
  let some (v₂, _) ← evalFin ev₂ | return none
  let some (v₃, _) ← evalFin ev₃ | return none
  return some ⟨r, c, [v₁, v₂, v₃], e⟩

def parseInnerPencilData (s : Q(Sudoku)) (e : Expr) : MetaM (Option InnerPencilData) := do
  match ← parseInnerPencilData₂ s e with
  | some d => return some d
  | none => parseInnerPencilData₃ s e

def getCellData (s : Q(Sudoku)) : MetaM (List CellData) := do
  let lCtx ← getLCtx
  lCtx.toList.filterMapM fun decl => parseCellData s decl.toExpr

def getOuterPencilData (s : Q(Sudoku)) : MetaM (List OuterPencilData) := do
  let lCtx ← getLCtx
  lCtx.toList.filterMapM fun decl => parseOuterPencilData s decl.toExpr

def getInnerPencilData (s : Q(Sudoku)) : MetaM (List InnerPencilData) := do
  let lCtx ← getLCtx
  lCtx.toList.filterMapM fun decl => parseInnerPencilData s decl.toExpr

def getBoardInfo (s : Q(Sudoku)) : MetaM BoardInfo := do
  let cellData ← getCellData s
  let outerPencilData ← getOuterPencilData s
  let innerPencilData ← getInnerPencilData s
  return ⟨cellData, outerPencilData, innerPencilData⟩

theorem Fin.ne_of_mod_ne {i j : Fin 9} {n m : Nat}
    (hi : i = ↑n) (hj : j = ↑m) (h : n % 9 ≠ m % 9) : i ≠ j := by
  apply Fin.ne_of_val_ne
  simpa [hi, hj]

def showByNormNum (goal : Q(Prop)) : MetaM Q($goal) := do
  let mvarId ← mkFreshMVarId
  let newGoal ← mkFreshExprMVarWithId mvarId (some goal)
  let .none ← Mathlib.Meta.NormNum.normNumAt mvarId {} #[]
    | throwError "bug in Tactic.Sudoku: norm_num failed to prove definitional equality"
  return newGoal

def mkRowConflict (s : Q(Sudoku)) (l r : CellData) : MetaM Q(False) := do
  logInfo m!"mkRowConflict {l} {r} {l.ce} {r.ce}"
  guard (l.row = r.row)
  guard (l.val = r.val)
  guard (l.col ≠ r.col)
  let neProof ← showByNormNum q($l.ce % 9 ≠ $r.ce % 9)
  let le : Q(Sudoku.f $s ($l.re, $l.ce) = $l.ve) := l.e
  let re : Q(Sudoku.f $s ($l.re, $r.ce) = $l.ve) := r.e
  let lcLit : Q(ℕ) := mkNatLit l.col
  let rcLit : Q(ℕ) := mkNatLit r.col
  let lhc : Q($lcLit = $l.ce) := l.hc
  let rhc : Q($rcLit = $r.ce) := r.hc
  return q(Sudoku.row_conflict $s $le $re (Fin.ne_of_mod_ne lhc rhc $neProof))

def mkColConflict (s : Q(Sudoku)) (l r : CellData) : MetaM Q(False) := do
  guard (l.row ≠ r.row)
  guard (l.val = r.val)
  guard (l.col = r.col)
  let neProof ← showByNormNum q($l.re ≠ $r.re)
  let le : Q(Sudoku.f $s ($l.re, $l.ce) = $l.ve) := l.e
  let re : Q(Sudoku.f $s ($r.re, $l.ce) = $l.ve) := r.e
  return q(Sudoku.col_conflict $s $le $re $neProof)

def mkCellConflict (s : Q(Sudoku)) (l r : CellData) : MetaM Q(False) := do
  logInfo m!"mkCellConflict {l} {r}"
  guard (l.row = r.row)
  guard (l.val ≠ r.val)
  guard (l.col = r.col)
  let neProof ← showByNormNum q($l.ve ≠ $r.ve)
  let le : Q(Sudoku.f $s ($l.re, $l.ce) = $l.ve) := l.e
  let re : Q(Sudoku.f $s ($l.re, $l.ce) = $r.ve) := r.e
  return q(Sudoku.cell_conflict $s $le $re $neProof)

def mkBoxConflict (s : Q(Sudoku)) (l r : CellData) : MetaM Q(False) := do
  guard (l.val = r.val)
  guard (l.row / 3 = r.row / 3)
  guard (l.col / 3 = r.col / 3)
  guard (l.row ≠ r.row ∨ l.col ≠ r.col)

  let rowEqProof ← showByNormNum q(($l.re : Nat) / 3 = $r.re / 3)
  let colEqProof ← showByNormNum q(($l.ce : Nat) / 3 = $r.ce / 3)

  let orProof ← if l.row ≠ r.row then
    let neProof ← showByNormNum q($l.re ≠ $r.re)
    pure <| show Q($l.re ≠ $r.re ∨ $l.ce ≠ $r.ce) from q(Or.inl $neProof)
  else
    let neProof ← showByNormNum q($l.ce ≠ $r.ce)
    pure <| show Q($l.re ≠ $r.re ∨ $l.ce ≠ $r.ce) from q(Or.inr $neProof)

  let le : Q(Sudoku.f $s ($l.re, $l.ce) = $l.ve) := l.e
  let re : Q(Sudoku.f $s ($r.re, $r.ce) = $l.ve) := r.e
  return q(Sudoku.box_conflict $s $le $re $rowEqProof $colEqProof $orProof)

#check Sudoku.box_cases

-- Tries `f` on all pairs of values in `l`, returning upon the first success.
def _root_.List.firstPairM [Alternative m] (l : List α) (f : α → α → m β) : m β :=
  match l with
  | (x :: y :: _) => f x y
  | _ => failure
  -- f l[0]! l[1]!
  -- l.firstM fun left => l.firstM fun right => f left right

def rowConflict (s : Q(Sudoku)) (cd : List CellData) : MetaM Q(False) :=
  cd.firstPairM (mkRowConflict s)

def colConflict (s : Q(Sudoku)) (cd : List CellData) : MetaM Q(False) :=
  cd.firstPairM (mkColConflict s)

def cellConflict (s : Q(Sudoku)) (cd : List CellData) : MetaM Q(False) := do
  logInfo "in cellConflict"
  cd.firstPairM (mkCellConflict s)

def boxConflict (s : Q(Sudoku)) (cd : List CellData) : MetaM Q(False) :=
  cd.firstPairM (mkBoxConflict s)

def conflict : TacticM Unit :=
  liftMetaFinishingTactic fun goal => do
    let s ← getSudoku
    let cd ← getCellData s
    logInfo m!"cellData: {cd}"
    let falseGoal ← goal.exfalso
    logInfo "after exfalos"
    let proof ← rowConflict s cd -- <|> colConflict s cd <|> cellConflict s cd <|> boxConflict s cd
    falseGoal.assign proof

elab "sudoku_conflict" : tactic => conflict

example (s : Sudoku) (h1 : s.f (1, 1) = 1) (h2 : s.f (1, 2) = 1) : False := by
  sudoku_conflict

elab "my_norm_num" : tactic =>
  liftMetaFinishingTactic fun goal => do goal.assign (← showByNormNum (← goal.getType))

example : (1 : Fin 9) ≠ 2 := by apply Fin.ne_of_val_ne; simp only [Fin.isValue, Fin.val_one,
  Fin.val_two, ne_eq, OfNat.one_ne_ofNat, not_false_eq_true]

end Tactic.Sudoku
