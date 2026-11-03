import Proof.Wire_3_5.FinalPass.ThrSz1
import Proof.Wire_3_5.FinalPass.ThrPtRS33
import Proof.Wire_3_5.Primitive.Writers.CallIndexRBase

/-! # The THR call's sizes, part 3: the call's words (P3:3176-3178)

**`levelWord_le`** (stage 4's table: `M + 2 + (J+1)·(5·W_max + 5 + R)`, the decoder modulus `pow W ≤ 4W + 2`),
**`majW_le`** (the windows `W_j ≤ 16t + 20(t·B_* + 2)`, filt:majorant), **`primesWord_le`** (the primes' unary word
`≤ (c+1)²`), **`payOf_le`** (a circuit's top payload `≤ 4L + 2·sourceChildBound alg L + 7`, base's
`top_output_bytes`). Paper quantity: the call's words, whose lengths make the per-point evaluation polynomial
(P3:3176-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrSz
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.SupplierPipeline NearCubicWires.RepairOrdinary

theorem pow_le (W : ℕ) : ListEval.pow W ≤ 4 * W + 2 := by
  unfold ListEval.pow
  have := PrimAsm.CallIndexR.two_pow_clog_le_two_mul (2 * W + 1) (by omega)
  omega

theorem record_le (J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Wm R : ℕ) (hW : ∀ j, W j ≤ Wm)
    (hR : ∀ j, (row j).length ≤ R) (j : ℕ) : (ListEval.record J W row j).length ≤ 5 * Wm + 5 + R := by
  unfold ListEval.record ListEval.unary
  simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil]
  have hp := pow_le (ListEval.topW J W j)
  have ht : ListEval.topW J W j ≤ Wm := by
    unfold ListEval.topW; split_ifs
    · exact Nat.zero_le _
    · exact hW j
  have := hR j
  omega

theorem levelWord_le (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Wm R : ℕ) (hW : ∀ j, W j ≤ Wm)
    (hR : ∀ j, (row j).length ≤ R) :
    (ListEval.levelWord M J W row).length ≤ M + 2 + (J + 1) * (5 * Wm + 5 + R) := by
  unfold ListEval.levelWord ListEval.unary
  simp only [List.length_append, List.length_replicate, List.length_singleton, List.length_flatMap]
  have hs := List.sum_le_card_nsmul ((ListEval.levels J).map fun j => (ListEval.record J W row j).length)
    (5 * Wm + 5 + R) (fun x hx => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      exact record_le J W row Wm R hW hR j)
  rw [smul_eq_mul, List.length_map, ListEval.levels_length] at hs
  omega

theorem majW_le (P : Filters.MajorantParams) (j : ℕ) : P.W j ≤ 16 * P.t + 20 * (P.t * P.Bstar + 2) := by
  unfold Filters.MajorantParams.W
  have h1 := Nat.sqrt_le_self (P.t * P.Bstar)
  have h2 := Nat.div_le_self (Nat.sqrt (P.t * P.Bstar) + 1) (2 ^ (j / 2))
  omega

theorem primesWord_le (c : ℕ) :
    (PrimAsm.Data.unaryList (PrimThrW.Joins.primesList c)).length ≤ (c + 1) * (c + 1) := by
  rw [ThrPt.unaryList_length]
  have hmem : ∀ p ∈ PrimThrW.Joins.primesList c, p ≤ c := fun p hp => by
    unfold PrimThrW.Joins.primesList at hp
    rw [List.mem_filter, List.mem_range] at hp
    omega
  have hlen : (PrimThrW.Joins.primesList c).length ≤ c + 1 := by
    unfold PrimThrW.Joins.primesList
    exact (List.length_filter_le _ _).trans (by simp)
  exact (ThrPt.map_add_le c 1 _ hmem).trans (Nat.mul_le_mul_right _ hlen)

theorem payOf_le (alg : RepairRepresentation.DecompositionAlgorithm) {q : ℕ} (C : NormalizedThresholdThresholdCircuit q)
    (L : ℕ) (hd : C.descriptionBits ≤ L) :
    (PrimThrW.TopFront.payOf alg C).length ≤ 4 * L + 2 * RepairSource.CloseoutRawRows.sourceChildBound alg L + 7 := by
  unfold PrimThrW.TopFront.payOf
  rw [FinalPass.Tm.frame_eq_frameP, List.length_append, FinalPass.Tm.frameP_length, List.length_append,
    PrimT.natWord_length', List.length_singleton]
  have h1 := RepairSource.CloseoutRawRows.top_output_bytes alg C L hd
  have h2 : C.top.support.card ≤ L := by
    have := Finset.card_le_univ C.top.support
    simp only [Fintype.card_fin] at this
    have := count_bits C
    omega
  have h3 := nbl_le C.top.support.card
  omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrSz
