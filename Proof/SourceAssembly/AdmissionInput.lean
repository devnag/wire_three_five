import Proof.SourceAssembly.AdmissionRequest

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator NearCubicWires.PolynomialSchedule NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.CompilerSemantics
open NearCubicWires.RepairSource.CloseoutRawRows (descriptionEnvelope descriptionEnvelope_polynomial
  sourceChildBound sourceChildBound_polynomial symmetric_occurrences_description
  threshold_occurrences_description)
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open scoped BigOperators

noncomputable section

/-! ## 1. Word lengths -/

theorem natBitLength_le_succ (n : ℕ) : natBitLength n ≤ n+1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 n
  omega

theorem natWord_le (n : ℕ) : (natWord n).length ≤ 2*n+3 := by
  rw [RepairOrdinary.DecompositionSource.natWord_length]
  have := natBitLength_le_succ n
  omega

theorem bottomWord_le {q : ℕ} (g : SupportedNormalizedGate q) :
    (bottomWord g).length ≤ 2*q + 2*g.descriptionBits + 7 := by
  unfold bottomWord
  rw [RepairOrdinary.DecompositionSource.thresholdWord_length]
  have hs := CloseoutRawRows.strict_gate_bits g.gate
  have hb := natBitLength_le_succ q
  unfold SupportedNormalizedGate.descriptionBits
  omega

theorem flatMap_frame_length {α : Type} (xs : List α) (f : α → List Bool) :
    (xs.flatMap (fun x => RepairOrdinary.frame (f x))).length =
      (xs.map (fun x => 2*(f x).length+1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, RepairOrdinary.frame_length, List.map_cons,
      List.sum_cons, ih]

theorem flatMap_frame_le {α : Type} (xs : List α) (f : α → List Bool) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap (fun x => RepairOrdinary.frame (f x))).length ≤ xs.length * (2*B+1) := by
  rw [flatMap_frame_length]
  have hm : ∀ y ∈ xs.map (fun x => 2*(f x).length+1), y ≤ 2*B+1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have := h x hx
    omega
  simpa using List.sum_le_card_nsmul _ _ hm

theorem symWord_le {q : ℕ} (c : NormalizedSymmetricThresholdCircuit q) :
    (symWord c).length ≤ (4*q+23)*(c.descriptionBits+1) := by
  have hdesc : c.descriptionBits = c.bottomCount + 1 + ∑ i, (c.bottom i).descriptionBits := rfl
  have hsum : ((List.ofFn c.bottom).flatMap (fun g => RepairOrdinary.frame (bottomWord g))).length ≤
      c.bottomCount*(4*q+15) + 4*∑ i, (c.bottom i).descriptionBits := by
    rw [flatMap_frame_length, List.map_ofFn, List.sum_ofFn]
    calc (∑ i : Fin c.bottomCount, ((fun x => 2*(bottomWord x).length+1) ∘ c.bottom) i)
        ≤ ∑ i : Fin c.bottomCount, (4*q+15 + 4*(c.bottom i).descriptionBits) := by
          apply Finset.sum_le_sum
          intro i _
          have := bottomWord_le (c.bottom i)
          simp only [Function.comp]
          omega
      _ = c.bottomCount*(4*q+15) + 4*∑ i, (c.bottom i).descriptionBits := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
  unfold symWord
  simp only [List.length_append, RepairOrdinary.frame_length, List.length_ofFn]
  have hn := natWord_le c.bottomCount
  set S := ∑ i, (c.bottom i).descriptionBits
  rw [hdesc]
  nlinarith [Nat.zero_le (q*S), Nat.zero_le (q*c.bottomCount)]

theorem thrWord_le {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) :
    (thrWord c).length ≤ (4*q+4*c.descriptionBits+60)*(c.descriptionBits+1) := by
  have hdesc : c.descriptionBits = c.top.gate.encodingBits + c.bottomCount +
      ∑ i, (c.bottom i).descriptionBits := rfl
  set S := ∑ i, (c.bottom i).descriptionBits with hS
  have hcard : c.top.support.card ≤ c.bottomCount := by
    simpa using Finset.card_le_univ c.top.support
  have hwire : c.top.wireCount ≤ c.bottomCount := hcard
  have hone : ∀ j : Fin c.bottomCount, (c.bottom j).descriptionBits ≤ S :=
    fun j => Finset.single_le_sum (fun i _ => Nat.zero_le ((c.bottom i).descriptionBits))
      (Finset.mem_univ j)
  have hflat : ((List.ofFn (fun i => c.bottom (retainedTopIndex c i))).flatMap
      (fun g => RepairOrdinary.frame (bottomWord g))).length ≤
      c.top.support.card*(2*(2*q+2*S+7)+1) := by
    have h := flatMap_frame_le (List.ofFn (fun i => c.bottom (retainedTopIndex c i))) bottomWord
      (2*q+2*S+7) (by
        intro g hg
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
        have := bottomWord_le (c.bottom (retainedTopIndex c i))
        have := hone (retainedTopIndex c i)
        omega)
    simpa using h
  have htop := RepairOrdinary.DecompositionSource.thresholdWord_bound
    (nonStrictAsStrict (retainedTopGate c))
  have hs := CloseoutRawRows.strict_gate_bits (retainedTopGate c)
  have hr := CloseoutRawRows.retained_top_bits c
  have hn := natWord_le c.top.wireCount
  unfold thrWord
  simp only [List.length_append, RepairOrdinary.frame_length]
  rw [hdesc]
  nlinarith [Nat.zero_le (q*S), Nat.zero_le (q*c.bottomCount), Nat.zero_le (S*S),
    Nat.zero_le (c.bottomCount*c.bottomCount), Nat.zero_le (c.top.gate.encodingBits*S),
    Nat.zero_le (q*c.top.gate.encodingBits), Nat.zero_le (c.bottomCount*S),
    Nat.zero_le (c.top.gate.encodingBits*c.bottomCount),
    Nat.zero_le (c.top.gate.encodingBits*c.top.gate.encodingBits)]

/-! ## 2. The five framed fields of `Request.input` -/

/-! ## 3. `h_input` -/


end
end NearCubicWires.Admission
