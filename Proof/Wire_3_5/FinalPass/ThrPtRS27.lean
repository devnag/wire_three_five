import Proof.Wire_3_5.FinalPass.ThrPtRS26
import Proof.Wire_3_5.Primitive.SeedFix.TabThrLayout

/-! # S2 (THR per point), part 41: the call's facts (P3:3170-3178)

The tuple's gate list `tupleG Cs` is the occurrences' gates (`thrOccs_gates`): **`occCorners_eq`** (the corner word
stage 2 writes is `occCorners`), `tupleG_len`. `thrH Cs`: the width stage 2 runs at (`tabH`, `0` without gates).
**`table_eq`**: with `a ≠ 0` the call's word 0 is `gatesW (thrH Cs) (tupleG Cs)`; **`table_read`**: the width
measurement reads `h` framed pairs and then `0`; **`thrH_hov`**: stage 2's accumulators do not overflow at width
`thrH Cs`. Paper quantity: the occurrences `𝒪` and their corner word (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline

section Call
variable (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)

theorem tuple_gates : (Primitive.thrOccs P Cs).map (·.gate) = PrimT.ThrTab.tupleG Cs :=
  PrimT.ThrTab.thrOccs_gates P Cs

theorem tupleG_len : (PrimT.ThrTab.tupleG Cs).length = (Primitive.thrOccs P Cs).length := by
  rw [← tuple_gates P Cs, List.length_map]

theorem occCorners_eq (c : BitInput P.n) (u v : P.Errors) :
    Term.occCorners P Cs c u v = Pop.cornerWord ((PrimT.ThrTab.tupleG Cs).map NormalizedThresholdGate.eval) c
      (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) := by
  unfold Term.occCorners
  rw [← tuple_gates P Cs, List.map_map]
  rfl

theorem tupleG_zero (h : a' = 0) : PrimT.ThrTab.tupleG Cs = [] := by
  subst h
  simp [PrimT.ThrTab.tupleG]

end Call

/-- Stage 2's width. -/
def thrH {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) : ℕ :=
  if PrimT.ThrTab.tupleG Cs = [] then 0 else PrimT.tabH (PrimT.ThrTab.tupleG Cs)

theorem gatesW_thrH {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) :
    Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs) =
      Corner.gatesW (thrH Cs) (PrimT.ThrTab.tupleG Cs) := by
  unfold thrH
  split_ifs with h
  · rw [h]; rfl
  · rfl

theorem fp_even (w : List Bool) : ∀ i < w.length, ∀ L : List Bool, (frameP w ++ L).getD (2 * i) false = true := by
  induction w with
  | nil => intro i hi; simp at hi
  | cons b w ih =>
    intro i hi L
    cases i with
    | zero => rfl
    | succ i =>
      rw [frameP_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih i (by simpa using hi) L

/-- **The width measurement's reads.** -/
theorem table_read {n : ℕ} (h : ℕ) (g : NormalizedThresholdGate n) (G : List (NormalizedThresholdGate n)) :
    (∀ i < h, readTapeBit (Corner.gatesW h (g :: G)) (1 + 2 * i) = true) ∧
      readTapeBit (Corner.gatesW h (g :: G)) (1 + 2 * h) = false := by
  obtain ⟨rest, hr⟩ : ∃ rest, Corner.gatesW h (g :: G) =
      true :: (frameP (RepairOrdinary.SignedSortKey.binary h (-g.threshold).toNat) ++ false :: rest) := by
    refine ⟨frame (RepairOrdinary.SignedSortKey.binary h (-(-g.threshold)).toNat) ++
      ((List.ofFn g.weight).flatMap (Corner.pairW h) ++ (G.flatMap (Corner.gateW h) ++ [false])), ?_⟩
    simp only [Corner.gatesW, Corner.gateW, Corner.pairW, List.flatMap_cons, frame_len, List.cons_append,
      List.append_assoc, List.singleton_append, List.nil_append]
  rw [hr]
  refine ⟨fun i hi => ?_, ?_⟩
  · unfold readTapeBit
    rw [show 1 + 2 * i = 2 * i + 1 by ring, List.getD_cons_succ]
    exact fp_even _ i (by rw [Corner.binary_length']; exact hi) _
  · have := rdMid (true :: frameP (RepairOrdinary.SignedSortKey.binary h (-g.threshold).toNat)) rest false
    simp only [List.length_cons, frameP_length, Corner.binary_length'] at this
    rw [show 1 + 2 * h = 2 * h + 1 by ring]
    simpa using this

theorem thrH_hov {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) :
    ∀ g ∈ PrimT.ThrTab.tupleG Cs,
      (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ thrH Cs ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ thrH Cs := by
  intro g hg
  unfold thrH
  rw [if_neg (List.ne_nil_of_mem hg)]
  exact PrimT.tab_hov _ g hg

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
