import Proof.Wire_3_5.UnionMachine.PlanBase
import Proof.Wire_3_5.Transfer.TransferUnionCompleteBase

/-! # C6 front, U5, the C1 dock: the union's selection request

"It then selects the common star translation" (P3:3673): the union's translation is `star:selection`'s first minimizer
over the weighted carriers `g.pops = [(p_X, carrier X)]` (`UnionGuess.translation`, P3:1360, 3413-3419). C1 (the plan's
`c1sized d` at `c1inst`) selects `selArgmin R = selectCodes (popsOf R)`.
* **`selReqOn g vs`**: `n = q`, `r = B.rOf q`, the gates = the listed variables' carriers' gates in order, each listed
  variable's population = its gates' index range and `p_X`;
* **`popsOf_selReqOn`**: `popsOf (selReqOn g vs) = vs.map (p_X, carrier X)`.

Paper quantity of the main types: the weighted carriers handed to `star:selection`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSelReq
open NearCubicWires NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine (popsOf gateOf selArgmin ParamsOk starParamsOf)

/-- A carrier's gate as the seed's integer gate. -/
def toInt {n : ℕ} (gt : NormalizedThresholdGate n) : IntGate n := ⟨gt.weight, gt.threshold⟩

/-! ## Flattened lists -/

/-- The start of item `i`'s segment in the concatenation of `f` over `l`. -/
def segStart {α β : Type} (f : α → List β) (l : List α) (i : ℕ) : ℕ := ((l.take i).map fun a => (f a).length).sum

theorem flat_seg {α β : Type} (f : α → List β) (l : List α) (i k : ℕ) (hi : i < l.length)
    (hk : k < (f l[i]).length) : (l.flatMap f)[segStart f l i + k]? = some (f l[i])[k] := by
  have hs : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i l]
    rw [List.drop_eq_getElem_cons hi]
  have hl : ((l.take i).flatMap f).length = segStart f l i := by simp [segStart, List.length_flatMap]
  have e : l.flatMap f = (l.take i).flatMap f ++ (f l[i] ++ (l.drop (i + 1)).flatMap f) := by
    conv_lhs => rw [hs]
    rw [List.flatMap_append, List.flatMap_cons]
  rw [e, List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel_left,
    List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

section Req

end Req

/-! ## Zero-weight populations -/

section Filter
variable (P : Shared.StarParams)

theorem sum_filter_zero (pops : List (ℚ × Stars.Carrier P.n)) (f : Stars.Carrier P.n → ℚ) :
    ((pops.filter fun p => p.1 ≠ 0).map fun p => p.1 * f p.2).sum = (pops.map fun p => p.1 * f p.2).sum := by
  induction pops with
  | nil => rfl
  | cons p ps ih =>
    simp only [ne_eq, decide_not] at ih ⊢
    by_cases h : p.1 = 0
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

/-- **Zero-weight populations change no objective.** -/
theorem objective_filter (σ : P.Translation) (pops : List (ℚ × Stars.Carrier P.n)) :
    P.starObjectiveRef σ (pops.filter fun p => p.1 ≠ 0) = P.starObjectiveRef σ pops := by
  unfold Shared.StarParams.starObjectiveRef
  rw [sum_filter_zero P pops (fun c => (c.map fun g => ∑ u : P.Errors, ∑ v : P.Errors, (P.rowCount σ g u v : ℚ)).sum)]

/-- **Zero-weight populations change no selection.** -/
theorem selectCodes_filter (pops : List (ℚ × Stars.Carrier P.n)) :
    P.selectCodes (pops.filter fun p => p.1 ≠ 0) = P.selectCodes pops := by
  unfold Shared.StarParams.selectCodes
  congr 1
  funext l
  exact objective_filter P _ pops

end Filter

/-! ## The union's request -/

section Union

end Union

/-! ## C1's precondition -/

section Pre

end Pre

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSelReq
