import Lean
import Proof.Wire_3_5.UnionMachine.PlanBase
import Proof.Wire_3_5.Transfer.TransferUnionComplete
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.FrontSelReqBase


noncomputable section
set_option maxRecDepth 4096


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

/-! ## Flattened lists -/

section Req
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

/-- **The selection request on a list of variables.** -/
noncomputable def selReqOn (vs : List (PcppVar g.pcpp)) : SelectionReq :=
  ⟨g.q, B.rOf g.q, (vs.flatMap g.carrier).map toInt,
    vs.mapIdx fun i X => (List.range' (segStart g.carrier vs i) (g.carrier X).length, g.weight X)⟩

theorem gates_get (vs : List (PcppVar g.pcpp)) (i k : ℕ) (hi : i < vs.length) (hk : k < (g.carrier vs[i]).length)
    (d : IntGate g.q) :
    ((vs.flatMap g.carrier).map toInt).getD (segStart g.carrier vs i + k) d = toInt (g.carrier vs[i])[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, flat_seg g.carrier vs i k hi hk]
  rfl

/-- **The request's populations are the listed variables' weighted carriers.** -/
theorem popsOf_selReqOn (vs : List (PcppVar g.pcpp)) :
    popsOf (selReqOn g vs) = vs.map fun X => (g.weight X, g.carrier X) := by
  apply List.ext_getElem
  · simp [popsOf, selReqOn]
  · intro i h1 h2
    have hi : i < vs.length := by simpa [popsOf, selReqOn] using h1
    simp only [popsOf, selReqOn, List.getElem_map, List.getElem_mapIdx, Prod.mk.injEq, true_and]
    apply List.ext_getElem
    · simp
    · intro k k1 k2
      simp only [List.getElem_map, List.getElem_range', one_mul]
      rw [gates_get g vs i k hi (by simpa using k1)]
      rfl

end Req

/-! ## Zero-weight populations -/

section Filter

end Filter

/-! ## The union's request -/

section Union
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

/-- The variables of positive weight, in order. -/
noncomputable def vsPos : List (PcppVar g.pcpp) :=
  (List.finRange (g.pcpp.systematicBits + g.pcpp.auxiliaryBits)).filter fun X => g.weight X ≠ 0

/-- **The union's selection request**: the positive-weight variables. -/
noncomputable def selReqOf : SelectionReq := selReqOn g (vsPos g)

theorem popsOf_selReq : popsOf (selReqOf g) = g.pops.filter fun p => p.1 ≠ 0 := by
  unfold selReqOf
  rw [popsOf_selReqOn, UnionGuess.pops, vsPos, List.filter_map]
  rfl

/-- **C1's selection is the union's translation** where the star hypotheses hold. -/
theorem selArgmin_selReq (h : I.StarAt g.q) : selArgmin (selReqOf g) = g.translation := by
  have hP : ParamsOk (selReqOf g) := ⟨Nat.even_iff.mp h.1, h.2.1, h.2.2.1⟩
  unfold selArgmin UnionGuess.translation
  rw [dif_pos hP, dif_pos h]
  show (starParamsOf (selReqOf g) hP).selectCodes (popsOf (selReqOf g)) = (I.starParams g.q h).selectCodes g.pops
  rw [popsOf_selReq g]
  exact selectCodes_filter (I.starParams g.q h) g.pops

end Union

/-! ## C1's precondition -/

section Pre
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

theorem pops_snd (vs : List (PcppVar g.pcpp)) : (selReqOn g vs).pops.map Prod.snd = vs.map g.weight := by
  apply List.ext_getElem
  · simp [selReqOn]
  · intro i h1 h2
    simp [selReqOn, List.getElem_mapIdx]

theorem sum_filter_weight (l : List (PcppVar g.pcpp)) :
    ((l.filter fun X => g.weight X ≠ 0).map g.weight).sum = (l.map g.weight).sum := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [ne_eq, decide_not] at ih ⊢
    by_cases h : g.weight X = 0
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

theorem sum_weight_q : ((List.finRange (g.pcpp.systematicBits + g.pcpp.auxiliaryBits)).map g.weight).sum = 1 := by
  have h := UnionGuess.sum_weight g
  rw [← Fin.sum_univ_def]
  exact_mod_cast h

/-- **C1's precondition** at the union's request, where the star hypotheses hold. -/
theorem pre_selReq (h : I.StarAt g.q) :
    (selReqOf g).r % 2 = 0 ∧ 2 ≤ (selReqOf g).r ∧ 4 * (selReqOf g).r ≤ (selReqOf g).n ∧
      ((selReqOf g).pops.map Prod.snd).sum = 1 ∧ ∀ X ∈ (selReqOf g).pops, 0 ≤ X.2 := by
  refine ⟨Nat.even_iff.mp h.1, h.2.1, h.2.2.1, ?_, ?_⟩
  · unfold selReqOf; rw [pops_snd, vsPos, sum_filter_weight, sum_weight_q]
  · intro X hX
    unfold selReqOf selReqOn at hX
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hX
    simp only [List.getElem_mapIdx]
    exact UnionGuess.weight_nonneg g _

end Pre

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSelReq

end
