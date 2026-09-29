import Proof.Wire_3_5.Selection.CosCls2

/-! # C1.5 class bound, part 3: all cosets (P3:1337-1359)

Paper: "There are `2^k` candidate cosets, so the total is bounded as claimed" (P3:1358-1359). Each coset evaluates
every population (`≤ L` of them, each `≤ L` gates, one gate routine per gate) and compares keys; the loop runs `2^k`
rounds. So the loop's cost is at most `K·W^a·2^k·2^{s·r/2}·2^{(n+1)/2}`, and the output of the selected coset's codes
costs at most `K·W^a·2^k`. Main declarations: `bd_idx`, `bd_pops`, `bd_cosetB`, **`bd_loop`**, **`bd_out`**. Paper
quantity: the `2^k` coset rounds. -/

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
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_gate)

theorem bd_idx {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h) :
    Bd ex (fun R h => idxCost (starParamsOf R h) R.n (Wof R) (Lof R) R.gates.length) := by
  refine bd_lift hex ?_
  unfold idxCost toUCost uRound fetchCost
  with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_idx)

theorem bd_popC {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h) :
    Bd ex (fun R h => popCost (starParamsOf R h) R.n (Wof R) (Lof R) R.gates.length (Lof R)) := by
  refine bd_lift hex ?_
  unfold popCost ratStepCost mulCost
  with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_popC)

theorem popCost_mono (P : StarParams) (n W V g m M : ℕ) (hm : m ≤ M) : popCost P n W V g m ≤ popCost P n W V g M := by
  unfold popCost
  gcongr

theorem popsCost_le (P : StarParams) (n W V g M : ℕ) :
    ∀ ps : List (List ℕ × ℚ), (∀ X ∈ ps, X.1.length ≤ M) →
      popsCost P n W V g ps ≤ ps.length * (popCost P n W V g M + 4) + 1
  | [], _ => by simp [popsCost]
  | X :: ps, hX => by
    have ih := popsCost_le P n W V g M ps (fun Y hY => hX Y (by simp [hY]))
    have h1 := popCost_mono P n W V g _ M (hX X (by simp))
    simp only [popsCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- All populations of one coset. -/
theorem bd_pops {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h) :
    Bd ex (fun R h => popsCost (starParamsOf R h) R.n (Wof R) (Lof R) R.gates.length R.pops) := by
  refine bd_mono (g := fun R h => R.pops.length *
    (popCost (starParamsOf R h) R.n (Wof R) (Lof R) R.gates.length (Lof R) + 4) + 1)
    (fun R h => popsCost_le _ _ _ _ _ _ R.pops (fun X hX => (pop_bits R X hX).2.2.2)) ?_
  refine bd_lift hex ?_
  with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_pops)

theorem bd_cosetB {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h) :
    Bd ex (fun R h => cosetBCost (starParamsOf R h) R.n (Wof R) (Lof R) R.gates.length (R.r * R.s) R.pops.length
      (popTable (Wof R) R).length R.pops) := by
  refine bd_lift hex ?_
  unfold cosetBCost ratLtCost mulCost
  with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_cosetB)

/-- **All `2^k` cosets.** -/
theorem bd_loop : Bd eK (fun R h => loopCost R h) := by
  unfold loopCost iterCost
  with_reducible cos_bd

/-- **The selected coset's codes.** -/
theorem bd_out : Bd eK (fun R _ => outCost R.r R.s) := by
  unfold outCost codeCost rawCost
  with_reducible cos_bd

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
