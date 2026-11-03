import Proof.Wire_3_5.Primitive.Writers.ThrSide5Base

/-! # PA2 c4 THR block, piece 6 part 6: the THR pool's coefficient width and dense pool (twin of the SymPool)

"Constants, complemented atoms, and the systematic encoding parity are permitted at the same fixed description
envelope" (P3:3092-3094) and alg:disjoint's child bits (P3:1596-1615): at a THR call every pool gate (a carrier atom,
its complement `negGate`, or an occurrence of a circuit's bottom gate) has at most `(n+1)^{26} + 1` encoding bits, so
the decomposition algorithm's budget at every pool gate is at most `symBud a n`; hence the pool fits any `h`
with `symBud a n + n + 2 ≤ h` (`PoolFit.poolFits_of`, generic in `h`: THR's and HASH's `h` alike), and the
dense pool has at most `2^{k + cDa·L}` children.

* **`thrPool_bits`**, **`thr_budget_le`**, **`thr_fits_of`**, **`thrD_le`**.

Paper quantities of the main types: the THR pool's coefficient bits against `h`, the THR dense pool's size. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (symBud symBud_le' cDa enc_negGate enc_nonStrict n2_le_L one_le_L densePool_length_le)

/-- **Every THR pool gate has at most `(n+1)^{26} + 1` encoding bits** (the call's envelopes). -/
theorem thrPool_bits (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (hcar : ∀ X ∈ carriers, X.WithinEnvelope 26)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) :
    ∀ g ∈ Records.thrPool P Cs carriers, g.encodingBits ≤ (P.n + 1) ^ 26 + 1 := by
  intro g hg
  unfold Records.thrPool Records.thrSlices at hg
  obtain ⟨sl, hsl, hg⟩ := List.mem_flatten.mp hg
  rcases List.mem_append.mp hsl with hX | hO
  · obtain ⟨X, hXc, rfl⟩ := List.mem_map.mp hX
    unfold FinalPass.Corner.maskGates at hg
    obtain ⟨g0, hg0, hgg⟩ := List.mem_flatMap.mp hg
    have hb := (hcar X hXc).2 g0 hg0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgg
    rcases hgg with rfl | rfl
    · omega
    · have := enc_negGate g0; omega
  · rw [List.mem_singleton] at hO
    subst hO
    rw [PrimT.ThrTab.thrOccs_gates] at hg
    obtain ⟨sl2, hsl2, hg2⟩ := List.mem_flatten.mp hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hsl2
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hg2
    unfold SupplierEstimator.thresholdCircuitOccurrences at ho
    obtain ⟨idx, rfl⟩ := List.mem_ofFn.mp ho
    have h1 := hd j
    unfold NormalizedThresholdThresholdCircuit.descriptionBits at h1
    have key : ∀ i, ((Cs j).bottom i).gate.encodingBits ≤ (P.n + 1) ^ 26 + 1 := by
      intro i
      have h2 : ((Cs j).bottom i).descriptionBits ≤ ∑ k, ((Cs j).bottom k).descriptionBits :=
        Finset.single_le_sum (f := fun k => ((Cs j).bottom k).descriptionBits) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      have h3 : ((Cs j).bottom i).gate.encodingBits ≤ ((Cs j).bottom i).descriptionBits := Nat.le_add_right _ _
      omega
    exact key _

/-- **Every THR pool gate's decomposition budget is at most `symBud a n`.** -/
theorem thr_budget_le (a : RepairRepresentation.DecompositionAlgorithm) (P : StarParams) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (hcar : ∀ X ∈ carriers, X.WithinEnvelope 26) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) :
    ∀ g ∈ (Records.thrPool P Cs carriers).map PrimT.C4Geo.suppG,
      RepairOrdinary.DecompositionSource.sourceBudget a (ExtDecompositionBatch.request g) ≤ symBud a P.n := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  have hb := thrPool_bits P Cs carriers hcar hd g0 hg0
  have hn := enc_nonStrict g0
  unfold RepairOrdinary.DecompositionSource.sourceBudget symBud
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  show P.n + (CompilerSemantics.nonStrictAsStrict g0).encodingBits + 1 ≤ _
  omega

/-- **The THR pool's three fits** at any `h ≥ symBud a n + n + 2` (THR's and HASH's `h` alike). -/
theorem thr_fits_of (a : RepairRepresentation.DecompositionAlgorithm) (P : StarParams) (σ : P.Translation) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (hcar : ∀ X ∈ carriers, X.WithinEnvelope 26) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26)
    (h Q psi : ℕ) (hh : symBud a P.n + P.n + 2 ≤ h) :
    Pool.CoefFit a (PrimT.C4Geo.poolReq P σ (Records.thrPool P Cs carriers) h Q psi) ∧
      Req.PNFit a (PrimT.C4Geo.poolReq P σ (Records.thrPool P Cs carriers) h Q psi) ∧
      Req.DenseFit h (Pool.densePool a (PrimT.C4Geo.poolReq P σ (Records.thrPool P Cs carriers) h Q psi).gates
        (PrimT.C4Geo.side P) (PrimT.C4Geo.width P) (PrimT.C4Geo.flips P σ)) :=
  FinalPass.PoolFit.poolFits_of a (PrimT.C4Geo.poolReq P σ (Records.thrPool P Cs carriers) h Q psi) (symBud a P.n)
    (thr_budget_le a P Cs carriers hcar hd) hh

section Gate

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
