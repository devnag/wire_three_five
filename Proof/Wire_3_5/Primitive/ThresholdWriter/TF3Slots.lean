import Proof.Wire_3_5.Primitive.ThresholdWriter.TF3Pay

/-! # TopFrontPort3 body, part 5: the four slots in sequence (`pays`, `pays_run`)

P3:2543-2551 and P3:3071-3091: every circuit `i < a'` of the call gets its payload `payOf alg (Cs i)` and native word
`thrWord (Cs i)`; the slots `i ≥ a'` are empty. The four slot stages run in sequence on disjoint docks, so each keeps
what the others wrote:

* `slotCost`, `paysCost`; **`slot_gen`** (one slot, filled or empty); `pays`; **`pays_run`**: from a bank whose
  filled slots hold the payload machine's entry at heads `0` and whose empty slots have a blank first cell, every
  filled slot's payload and native word on its dock's `outTop`/`1692`, the empty slots' docks unchanged, every tape
  outside the docks unchanged.

Paper quantities of the main type: the payloads `payOf alg (Cs i)` and native words `thrWord (Cs i)`, `i < a'`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TF3Slots
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.PrimThrW.TF3Pay

variable (a : DecompositionAlgorithm)

/-- The native word's tape in the payload machine. -/
def t1692 : Fin (PayM.PT a) := ⟨1692, by show 1692 < 1781 + (PayM.Ta a - 1); omega⟩

/-- One slot's cost. -/
noncomputable def slotCost (L : ℕ) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (i : Fin 4) : ℕ :=
  if h : i.val < a' then ThrTab.thrBlockCost (Cs ⟨i.val, h⟩) L + 1 + PayM.topBudget a (Cs ⟨i.val, h⟩) + 2 else 2

/-- The four slots' cost. -/
noncomputable def paysCost (L : ℕ) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) : ℕ :=
  slotCost a L Cs 0 + 1 + (slotCost a L Cs 1 + 1 + (slotCost a L Cs 2 + 1 + slotCost a L Cs 3))

/-- **The four slot stages.** -/
noncomputable def pays :=
  Composition.machine (payI a 0) (Composition.machine (payI a 1) (Composition.machine (payI a 2) (payI a 3)))

/-- **One slot**, filled or empty. -/
theorem slot_gen (i : Fin 4) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (L : ℕ)
    (hL : ∀ j, (Cs j).descriptionBits ≤ L) (H : Fin (TT a) → ℕ) (A : Fin (TT a) → List Bool)
    (hf : ∀ h : i.val < a', (∀ k, A (payMap a i k) =
      PayM.payIn a (encodeNormalizedThresholdThresholdCircuit (Cs ⟨i.val, h⟩)) n L k) ∧ ∀ k, H (payMap a i k) = 0)
    (hb : a' ≤ i.val → A (dT a (sTape (nr := DR) (sSym i 0))) = []) :
    ∃ (H' : Fin (TT a) → ℕ) (A' : Fin (TT a) → List Bool), Step (payI a i) (slotCost a L Cs i) H A H' A' ∧
      (∀ t, (∀ k, payMap a i k ≠ t) → H' t = H t ∧ A' t = A t) ∧
      (∀ h : i.val < a', A' (payMap a i (PayM.outTop a)) = TopFront.payOf a (Cs ⟨i.val, h⟩) ∧
        A' (payMap a i (t1692 a)) = PCJd4d1d9d7d1fa4313_Production.thrWord (Cs ⟨i.val, h⟩)) ∧
      (a' ≤ i.val → ∀ t, A' t = A t) := by
  by_cases hi : i.val < a'
  · obtain ⟨hA, hH⟩ := hf hi
    obtain ⟨H', A', s, hk, -, h1, h2⟩ := payI_filled a i (Cs ⟨i.val, hi⟩) L (hL _) H A hH hA
    refine ⟨H', A', ?_, hk, fun _ => ⟨h1, h2⟩, fun h => absurd hi (by omega)⟩
    unfold slotCost
    rw [dif_pos hi]
    exact s
  · refine ⟨H, A, ?_, fun t _ => ⟨rfl, rfl⟩, fun h => absurd h hi, fun _ _ => rfl⟩
    unfold slotCost
    rw [dif_neg hi]
    exact payI_blank a i H A (hb (by omega))

/-- **The four slots.** -/
theorem pays_run {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (L : ℕ)
    (hL : ∀ j, (Cs j).descriptionBits ≤ L) (H : Fin (TT a) → ℕ) (A : Fin (TT a) → List Bool)
    (hf : ∀ i : Fin 4, ∀ h : i.val < a', (∀ k, A (payMap a i k) =
      PayM.payIn a (encodeNormalizedThresholdThresholdCircuit (Cs ⟨i.val, h⟩)) n L k) ∧ ∀ k, H (payMap a i k) = 0)
    (hb : ∀ i : Fin 4, a' ≤ i.val → A (dT a (sTape (nr := DR) (sSym i 0))) = []) :
    ∃ (H' : Fin (TT a) → ℕ) (A' : Fin (TT a) → List Bool), Step (pays a) (paysCost a L Cs) H A H' A' ∧
      (∀ t, (∀ i k, payMap a i k ≠ t) → A' t = A t) ∧
      (∀ i : Fin 4, ∀ h : i.val < a', A' (payMap a i (PayM.outTop a)) = TopFront.payOf a (Cs ⟨i.val, h⟩) ∧
        A' (payMap a i (t1692 a)) = PCJd4d1d9d7d1fa4313_Production.thrWord (Cs ⟨i.val, h⟩)) ∧
      (∀ i : Fin 4, a' ≤ i.val → ∀ k, A' (payMap a i k) = A (payMap a i k)) := by
  have d : ∀ (i i' : Fin 4), i ≠ i' → ∀ k k', payMap a i k ≠ payMap a i' k' := fun i i' h => payMap_disj a i i' h
  have z : ∀ i : Fin 4, dT a (sTape (nr := DR) (sSym i 0)) = payMap a i ⟨0, by unfold PayM.PT; omega⟩ :=
    fun i => (payMap_zero a i).symm
  -- slot 0
  obtain ⟨H1, A1, s0, k0, p0, b0⟩ := slot_gen a 0 Cs L hL H A (hf 0) (hb 0)
  have t0 : ∀ i : Fin 4, i ≠ 0 → ∀ k, H1 (payMap a i k) = H (payMap a i k) ∧ A1 (payMap a i k) = A (payMap a i k) :=
    fun i hi k => k0 _ (fun k' => d 0 i (Ne.symm hi) k' k)
  -- slot 1
  obtain ⟨H2, A2, s1, k1, p1, b1⟩ := slot_gen a 1 Cs L hL H1 A1
    (fun h => ⟨fun k => ((t0 1 (by decide) k).2).trans ((hf 1 h).1 k),
      fun k => ((t0 1 (by decide) k).1).trans ((hf 1 h).2 k)⟩)
    (fun h => by rw [z 1, (t0 1 (by decide) _).2, ← z 1]; exact hb 1 h)
  have t1 : ∀ i : Fin 4, i ≠ 1 → ∀ k, H2 (payMap a i k) = H1 (payMap a i k) ∧ A2 (payMap a i k) = A1 (payMap a i k) :=
    fun i hi k => k1 _ (fun k' => d 1 i (Ne.symm hi) k' k)
  -- slot 2
  obtain ⟨H3, A3, s2, k2, p2, b2⟩ := slot_gen a 2 Cs L hL H2 A2
    (fun h => ⟨fun k => ((t1 2 (by decide) k).2).trans (((t0 2 (by decide) k).2).trans ((hf 2 h).1 k)),
      fun k => ((t1 2 (by decide) k).1).trans (((t0 2 (by decide) k).1).trans ((hf 2 h).2 k))⟩)
    (fun h => by rw [z 2, (t1 2 (by decide) _).2, (t0 2 (by decide) _).2, ← z 2]; exact hb 2 h)
  have t2 : ∀ i : Fin 4, i ≠ 2 → ∀ k, H3 (payMap a i k) = H2 (payMap a i k) ∧ A3 (payMap a i k) = A2 (payMap a i k) :=
    fun i hi k => k2 _ (fun k' => d 2 i (Ne.symm hi) k' k)
  -- slot 3
  obtain ⟨H4, A4, s3, k3, p3, b3⟩ := slot_gen a 3 Cs L hL H3 A3
    (fun h => ⟨fun k => ((t2 3 (by decide) k).2).trans (((t1 3 (by decide) k).2).trans
        (((t0 3 (by decide) k).2).trans ((hf 3 h).1 k))),
      fun k => ((t2 3 (by decide) k).1).trans (((t1 3 (by decide) k).1).trans
        (((t0 3 (by decide) k).1).trans ((hf 3 h).2 k)))⟩)
    (fun h => by
      rw [z 3, (t2 3 (by decide) _).2, (t1 3 (by decide) _).2, (t0 3 (by decide) _).2, ← z 3]; exact hb 3 h)
  have t3 : ∀ i : Fin 4, i ≠ 3 → ∀ k, A4 (payMap a i k) = A3 (payMap a i k) :=
    fun i hi k => (k3 _ (fun k' => d 3 i (Ne.symm hi) k' k)).2
  refine ⟨H4, A4, s0.seq (s1.seq (s2.seq s3)), ?_, ?_, ?_⟩
  · intro t ht
    rw [(k3 t (ht 3)).2, (k2 t (ht 2)).2, (k1 t (ht 1)).2, (k0 t (ht 0)).2]
  · intro i h
    fin_cases i
    · show A4 (payMap a 0 (PayM.outTop a)) = TopFront.payOf a (Cs ⟨0, h⟩) ∧
        A4 (payMap a 0 (t1692 a)) = PCJd4d1d9d7d1fa4313_Production.thrWord (Cs ⟨0, h⟩)
      obtain ⟨e1, e2⟩ := p0 h
      exact ⟨by rw [t3 0 (by decide), (t2 0 (by decide) _).2, (t1 0 (by decide) _).2]; exact e1,
        by rw [t3 0 (by decide), (t2 0 (by decide) _).2, (t1 0 (by decide) _).2]; exact e2⟩
    · show A4 (payMap a 1 (PayM.outTop a)) = TopFront.payOf a (Cs ⟨1, h⟩) ∧
        A4 (payMap a 1 (t1692 a)) = PCJd4d1d9d7d1fa4313_Production.thrWord (Cs ⟨1, h⟩)
      obtain ⟨e1, e2⟩ := p1 h
      exact ⟨by rw [t3 1 (by decide), (t2 1 (by decide) _).2]; exact e1,
        by rw [t3 1 (by decide), (t2 1 (by decide) _).2]; exact e2⟩
    · show A4 (payMap a 2 (PayM.outTop a)) = TopFront.payOf a (Cs ⟨2, h⟩) ∧
        A4 (payMap a 2 (t1692 a)) = PCJd4d1d9d7d1fa4313_Production.thrWord (Cs ⟨2, h⟩)
      obtain ⟨e1, e2⟩ := p2 h
      exact ⟨by rw [t3 2 (by decide)]; exact e1, by rw [t3 2 (by decide)]; exact e2⟩
    · exact p3 h
  · intro i h k
    fin_cases i
    · show A4 (payMap a 0 k) = A (payMap a 0 k)
      rw [t3 0 (by decide), (t2 0 (by decide) _).2, (t1 0 (by decide) _).2, b0 h]
    · show A4 (payMap a 1 k) = A (payMap a 1 k)
      rw [t3 1 (by decide), (t2 1 (by decide) _).2, b1 h, (t0 1 (by decide) _).2]
    · show A4 (payMap a 2 k) = A (payMap a 2 k)
      rw [t3 2 (by decide), b2 h, (t1 2 (by decide) _).2, (t0 2 (by decide) _).2]
    · show A4 (payMap a 3 k) = A (payMap a 3 k)
      rw [b3 h, (t2 3 (by decide) _).2, (t1 3 (by decide) _).2, (t0 3 (by decide) _).2]

end NearCubicWires.WireExponent3_5.PrimThrW.TF3Slots
