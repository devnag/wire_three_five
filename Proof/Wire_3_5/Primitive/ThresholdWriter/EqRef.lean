import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins
import Proof.Packets.PacketsMetaCutoffMath

/-! # THR, EqW value layer: the equation word of selection `g`, circuit by circuit (`eqRef`, `eqWord_thrRealize`)

P3:2543-2551 (row:threshold-rows): `L_g` is the canonical stack of the selected children's equations, each embedded at
its circuit's occurrence block, with base `1 + Σ_i ‖child_i‖` (`ThresholdRows.equation`, `canonicalEquationStack`). The
equation writer streams it circuit by circuit, so its reference is:

* `baseOf a r sel = Σ_i childMagnitude (child_i) + 1`;
* **`eqRef a r sel`** = `intW (Σ_i base^i·t_i)`, then for each circuit `i` in order and each local index `k` of its
  retained top, `intW (base^i·w_{i,k})`;
* **`eqWord_equation`**: `EqW.eqWord (ThresholdRows.equation a r sel) = eqRef a r sel`, hence (`eqWord_thrRealize`)
  the writer's target `eqWord (thrRealize P Cs alg g)` is `eqRef`;
* the list lemma `range_segments` (an index range cut into consecutive blocks).

Paper quantity of the main type: the equation `L_g`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimThrW.EqRef
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary NearCubicWires.ThresholdAlignedEnvelope
open NearCubicWires.PacketsMeta.CutoffMath

/-! ## Consecutive blocks of an index range -/

/-- **An index range cut into consecutive blocks**, one per list entry, of lengths `h x`. -/
theorem range_segments {α β : Type} (h : β → ℕ) : ∀ (L : List β) (g : ℕ → α),
    (List.range (L.map h).sum).map g =
      (List.finRange L.length).flatMap (fun i =>
        (List.range (h (L.get i))).map (fun k => g (((L.map h).take i.val).sum + k)))
  | [], g => by simp
  | x :: rest, g => by
    rw [List.map_cons, List.sum_cons, List.range_add, List.map_append, List.map_map]
    change List.map g (List.range (h x)) ++ List.map (fun k => g (h x + k)) (List.range (List.map h rest).sum) =
      (List.finRange (rest.length + 1)).flatMap (fun i : Fin (rest.length + 1) =>
      (List.range (h ((x :: rest).get i))).map (fun k => g (((h x :: rest.map h).take i.val).sum + k)))
    rw [List.finRange_succ, List.flatMap_cons, range_segments h rest (fun k => g (h x + k)), List.flatMap_map]
    congr 1
    · simp
    · refine List.flatMap_congr fun i _ => ?_
      simp only [List.get_cons_succ, Fin.val_succ, List.take_succ_cons, List.sum_cons, Function.comp_apply]
      refine List.map_congr_left fun k _ => ?_
      congr 1
      omega

section Sel
variable (a : RepairRepresentation.DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (sel : ThresholdRows.Selection a r)

/-- The stack's base `1 + Σ_i ‖child_i‖`. -/
def baseOf : ℕ := (∑ i : Fin r.circuits.length, childMagnitude (child a r sel i)) + 1

theorem listBase_eq : equationListBase (ThresholdRows.equations a r sel) = ((baseOf a r sel : ℕ) : ℤ) :=
  canonical_base a r sel

theorem target_eq : (ThresholdRows.equation a r sel).target =
    ∑ i : Fin r.circuits.length, ((baseOf a r sel : ℕ) : ℤ) ^ i.val * (child a r sel i).target := by
  rw [canonical_target, listBase_eq]

/-- **The stacked weight at circuit `i`'s local index `k`** is `base^i·w_{i,k}`. -/
theorem weight_at (i : Fin r.circuits.length) (k : Fin (r.circuits.get i).top.support.card) :
    (ThresholdRows.equation a r sel).weights (thresholdCircuitEmbedding r i k) =
      ((baseOf a r sel : ℕ) : ℤ) ^ i.val * (child a r sel i).weight k := by
  rw [stack_weight_eq, listBase_eq, Finset.sum_eq_single i]
  · congr 1
    show embeddedWeight (thresholdCircuitEmbedding r i) (child a r sel i).weight (thresholdCircuitEmbedding r i k) = _
    unfold embeddedWeight
    rw [Finset.sum_eq_single k]
    · simp
    · intro x _ hx
      rw [if_neg (fun h => hx ((thresholdCircuitEmbedding r i).injective h))]
    · simp
  · intro i' _ hne
    show _ * embeddedWeight (thresholdCircuitEmbedding r i') (child a r sel i').weight
      (thresholdCircuitEmbedding r i k) = 0
    unfold embeddedWeight
    rw [Finset.sum_eq_zero, mul_zero]
    intro x _
    rw [if_neg (embedding_ne r i' i hne x k)]
  · simp

theorem occ_length : (thresholdFourfoldOccurrences r).length =
    (r.circuits.map fun c => c.top.support.card).sum := by
  unfold thresholdFourfoldOccurrences
  rw [List.length_flatMap]
  simp [thresholdCircuitOccurrences]

theorem start_eq (i : Fin r.circuits.length) :
    start r i = ((r.circuits.map fun c => c.top.support.card).take i.val).sum := by
  unfold start
  rw [List.length_flatMap, ← List.map_take]
  simp [thresholdCircuitOccurrences]

/-- **The stacked weights, circuit by circuit.** -/
theorem weights_blocks :
    List.ofFn (ThresholdRows.equation a r sel).weights =
      (List.finRange r.circuits.length).flatMap (fun i =>
        List.ofFn (fun k => ((baseOf a r sel : ℕ) : ℤ) ^ i.val * (child a r sel i).weight k)) := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℤ, g = fun p => if h : p < (thresholdFourfoldOccurrences r).length then
      (ThresholdRows.equation a r sel).weights ⟨p, h⟩ else 0 := ⟨_, rfl⟩
  have hl : List.ofFn (ThresholdRows.equation a r sel).weights = (List.range (thresholdFourfoldOccurrences r).length).map g := by
    apply List.ext_getElem
    · simp
    · intro p h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, hg]
      rw [dif_pos (by simpa using h1)]
  rw [hl, occ_length r, range_segments]
  refine List.flatMap_congr fun i _ => ?_
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hk : k < (r.circuits.get i).top.support.card := by simpa using h2
    have he := embedding_val r i ⟨k, hk⟩
    rw [← start_eq]
    have hlt : start r i + k < (thresholdFourfoldOccurrences r).length := by
      have := (thresholdCircuitEmbedding r i ⟨k, hk⟩).isLt
      rw [he] at this
      exact this
    rw [hg]
    simp only
    rw [dif_pos hlt]
    have hidx : (⟨start r i + k, hlt⟩ : Fin (thresholdFourfoldOccurrences r).length) =
        thresholdCircuitEmbedding r i ⟨k, hk⟩ := Fin.ext he.symm
    rw [hidx, weight_at]

end Sel

end NearCubicWires.WireExponent3_5.PrimThrW.EqRef
