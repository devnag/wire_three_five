import Proof.Wire_3_5.Primitive.SeedFix.TabThrLayout
import Proof.Wire_3_5.Primitive.SeedFix.TabThrScan
import Proof.CaseAnalysis.RawRowsThresholdSize

/-! # The THR call's sizes, part 1: the tuple's gates and occurrences (P3:3069-3072, 3176-3178)

With every circuit of the tuple within `L` description bits (the call's envelope `(n+1)^descDeg`, P3:3069-3072):
`bottom_bits`, `count_bits`, `occ_len` (a circuit's occurrences `≤` its description bits), **`occs_len`**
(`|occs| ≤ 4L`), **`tupleG_mem`** (a table gate is a bottom gate of a circuit), **`tabGW_len`** (a gate's native word
`≤ 4n + 9 + 4·bits`), **`tabH_le`** (stage 2's width `≤ 4L·(8n + 8L + 19)`). Paper quantity: the call's description
sizes, which make its per-point evaluation polynomial (P3:3176-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrSz
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.SupplierPipeline NearCubicWires.RepairOrdinary

theorem bottom_bits {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) (j : Fin C.bottomCount) :
    (C.bottom j).gate.encodingBits ≤ C.descriptionBits := by
  have h := Finset.single_le_sum (f := fun i => (C.bottom i).descriptionBits) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)
  unfold NormalizedThresholdThresholdCircuit.descriptionBits
  unfold SupportedNormalizedGate.descriptionBits at h ⊢
  omega

theorem count_bits {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) : C.bottomCount ≤ C.descriptionBits := by
  unfold NormalizedThresholdThresholdCircuit.descriptionBits SupportedNormalizedGate.descriptionBits
  omega

theorem occ_len {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) :
    (SupplierEstimator.thresholdCircuitOccurrences C).length ≤ C.descriptionBits := by
  unfold SupplierEstimator.thresholdCircuitOccurrences
  rw [List.length_ofFn]
  have h1 := Finset.card_le_univ C.top.support
  simp only [Fintype.card_fin] at h1
  have h2 := count_bits C
  omega

theorem occs_len (P : Shared.StarParams) {a' : ℕ} (ha : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (L : ℕ) (hL : ∀ i, (Cs i).descriptionBits ≤ L) : (Primitive.thrOccs P Cs).length ≤ 4 * L := by
  unfold Primitive.thrOccs SupplierEstimator.thresholdFourfoldOccurrences
  rw [List.length_flatMap]
  simp only [Primitive.thrRequest]
  rw [List.map_ofFn, List.sum_ofFn]
  calc ∑ i, (List.length ∘ SupplierEstimator.thresholdCircuitOccurrences) (Cs i) ≤ ∑ _i : Fin a', L :=
        Finset.sum_le_sum (fun i _ => (occ_len (Cs i)).trans (hL i))
    _ = a' * L := by simp
    _ ≤ 4 * L := Nat.mul_le_mul_right _ ha

theorem tupleG_mem {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (g : NormalizedThresholdGate n)
    (hg : g ∈ PrimT.ThrTab.tupleG Cs) : ∃ i j, g = ((Cs i).bottom j).gate := by
  unfold PrimT.ThrTab.tupleG at hg
  obtain ⟨l, hl, hgl⟩ := List.mem_flatten.mp hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hgl
  unfold SupplierEstimator.thresholdCircuitOccurrences at ho
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
  exact ⟨i, _, rfl⟩

theorem nbl_le (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 x
  omega

theorem tabGW_len {n : ℕ} (g : NormalizedThresholdGate n) :
    (PrimT.tabGW g).length ≤ 4 * n + 9 + 4 * g.encodingBits := by
  rw [PrimT.tabGW_eq, List.length_append, List.length_append, PrimT.natWord_length', PrimT.intWord_length',
    List.length_flatMap]
  have hw : ((List.ofFn g.weight).map (fun z => (RepairRepresentation.intWord z).length)).sum =
      2 * (∑ i, intBitLength (g.weight i)) + 2 * n := by
    simp only [PrimT.intWord_length', List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [intBitLength, natBitLength]
    ring
  have ht : natBitLength (g.threshold - 1).natAbs ≤ intBitLength g.threshold + 1 := by
    have hm : (g.threshold - 1).natAbs ≤ g.threshold.natAbs + 1 := by
      simpa only [sub_eq_add_neg, Int.natAbs_neg, Int.natAbs_one] using Int.natAbs_add_le g.threshold (-1)
    exact (PolynomialClock.natBitLength_mono hm).trans (RepairSource.CloseoutRawRows.bits_succ _)
  have hn := nbl_le n
  unfold NormalizedThresholdGate.encodingBits
  rw [hw]
  omega

theorem tabH_le {n a' : ℕ} (ha : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (L : ℕ)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) :
    PrimT.tabH (PrimT.ThrTab.tupleG Cs) ≤ 4 * L * (8 * n + 8 * L + 19) := by
  have hlen : (PrimT.ThrTab.tupleG Cs).length ≤ 4 * L := by
    unfold PrimT.ThrTab.tupleG
    rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    calc ∑ i, (List.length ∘ fun j => (SupplierEstimator.thresholdCircuitOccurrences (Cs j)).map (·.gate)) i
        ≤ ∑ _i : Fin a', L := Finset.sum_le_sum (fun i _ => by
          show ((SupplierEstimator.thresholdCircuitOccurrences (Cs i)).map (·.gate)).length ≤ L
          rw [List.length_map]; exact (occ_len _).trans (hL i))
      _ = a' * L := by simp
      _ ≤ 4 * L := Nat.mul_le_mul_right _ ha
  unfold PrimT.tabH PrimT.tabSeg
  rw [List.length_flatMap]
  have hsum := List.sum_le_card_nsmul ((PrimT.ThrTab.tupleG Cs).map fun g => (frame (PrimT.tabGW g)).length)
    (8 * n + 8 * L + 19) (fun x hx => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, j, rfl⟩ := tupleG_mem Cs g hg
      have h1 := tabGW_len ((Cs i).bottom j).gate
      have h2 := (bottom_bits (Cs i) j).trans (hL i)
      rw [FinalPass.Tm.frame_eq_frameP, List.length_append, FinalPass.Tm.frameP_length, List.length_singleton]
      omega)
  rw [smul_eq_mul, List.length_map] at hsum
  exact hsum.trans (Nat.mul_le_mul_right _ hlen)

end NearCubicWires.WireExponent3_5.FinalPass.ThrSz
