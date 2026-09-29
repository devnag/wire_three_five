import Proof.Wire_3_5.Selection.CosCls1

/-! # C1.5 class bound, part 2: one gate at one coset (P3:1340-1356)

Paper: "the number of candidate pairs for one gate is at most `2^{n/2}`-ish per side times the error rows"
(P3:1340-1356): the gate routine enumerates one side's points (`2^{lw}`, `2^{rw}`, at most `2^{(n+1)/2}`) against one
side's error rows (`2^{s·hh}`), joins by sorting records of width `W`, and scans. Its cost `gateCost P W V` is at most
`K·W^a·2^{s·r/2}·2^{(n+1)/2}` with `K`, `a` independent of the request. Main declarations: `bd_join`, `bd_phY`,
`bd_phL`, `bd_pre`, **`bd_gate`**. Paper quantity: the per-gate enumeration time. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Point NearCubicWires.WireExponent3_5.SelectionMachine.Sort

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_kw)

/-- The join of `m` records of width `W`. -/
theorem bd_join {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, 1 ≤ ex R h)
    {m : (R : SelectionReq) → ParamsOk R → ℕ} (hm : Bd ex m) : Bd ex (fun R h => joinCost (Wof R) (m R h)) := by
  unfold joinCost sortCost rc scanCost
  with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_join)

theorem bd_phY {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h) :
    Bd ex (fun R h => phYCost (starParamsOf R h) (Wof R) (keysY (starParamsOf R h))) := by
  refine bd_lift hex ?_
  unfold phYCost keysY
  with_reducible cos_bd

theorem bd_lvl {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h) :
    Bd ex (fun R h => lvlCost (starParamsOf R h) (Wof R) (keysL (starParamsOf R h))) := by
  refine bd_lift hex ?_
  unfold lvlCost keysL
  with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_lvl)

theorem bd_phL {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h) :
    Bd ex (fun R h => phLCost (starParamsOf R h) (Wof R) (Lof R) (keysL (starParamsOf R h))) := by
  refine bd_lift hex ?_
  unfold phLCost
  with_reducible cos_bd

theorem bd_consts {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h) :
    Bd ex (fun R h => constsCost (Wof R) (Lof R) (hh (starParamsOf R h)) (starParamsOf R h).b (starParamsOf R h).s
      (fL (starParamsOf R h)) (fR (starParamsOf R h))) := by
  refine bd_lift hex ?_
  unfold constsCost
  with_reducible cos_bd

theorem bd_tabL {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, 1 ≤ ex R h) :
    Bd ex (fun R h => tabLCost (starParamsOf R h) (Wof R)) := by
  refine bd_liftP hex ?_
  unfold tabLCost tabBlocksCost
  with_reducible cos_bd

theorem bd_tabR {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, 1 ≤ ex R h) :
    Bd ex (fun R h => tabRCost (starParamsOf R h) (Wof R)) := by
  refine bd_liftP hex ?_
  unfold tabRCost tabBlocksCost
  with_reducible cos_bd

theorem bd_zws {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, 1 ≤ ex R h) :
    Bd ex (fun R h => zwsCost (hh (starParamsOf R h) * (starParamsOf R h).b + fL (starParamsOf R h) + 1)
      (hh (starParamsOf R h) * (starParamsOf R h).s + 1) (starParamsOf R h).s (Wof R)) := by
  refine bd_liftP hex ?_
  unfold zwsCost
  with_reducible cos_bd

theorem bd_tk {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, 1 ≤ ex R h) :
    Bd ex (fun R h => tkCost (starParamsOf R h) (Wof R)) := by
  refine bd_liftP hex ?_
  unfold tkCost
  with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| first
    | cos_app bd_consts
    | cos_app bd_tabL
    | cos_app bd_tabR
    | cos_app bd_zws
    | cos_app bd_tk
    | cos_app bd_phY
    | cos_app bd_phL)

theorem bd_pre {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h) :
    Bd ex (fun R h => preCost (starParamsOf R h) (Wof R) (Lof R)) := by
  refine bd_lift hex ?_
  unfold preCost
  with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_pre)

/-- **One gate at one coset**: `gateCost ≤ K·W^a·2^{s·r/2}·2^{(n+1)/2}`. -/
theorem bd_gate {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h) :
    Bd ex (fun R h => gateCost (starParamsOf R h) (Wof R) (Lof R)) := by
  refine bd_lift hex ?_
  unfold gateCost gClrCost
  with_reducible cos_bd

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
