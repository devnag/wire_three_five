import Proof.Wire_3_5.FinalPass.ThrPtRS32

/-! # S2 (THR per point), part 47: the call's parameters are bounded by its size

`thrSize k = n + Σ|words| + Σ nums` (the seam's `ptSize`). Every parameter of the run is at most it: `n`, the
numbers `a, |𝒢|, τ₀, |occs|`, every prime (`p_le`), the primes' count, stage 4's `M` (`DM_le`), stage 2's width
(`H_le`), RowW's size `digsN ≤ 6·size` (`digsN_le`). Paper quantity: none beyond the machine model (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.SupplierPipeline

/-- The call's size. -/
def thrSize (k : Seams.ThrCall) : ℕ := k.P.n + (∑ i, (Seams.thrWords k i).length) + ∑ i, Seams.thrNums k i

variable (k : Seams.ThrCall)

theorem n_le : k.P.n ≤ thrSize k := by unfold thrSize; omega

theorem word_le (i : Fin 7) : (Seams.thrWords k i).length ≤ thrSize k := by
  have := Finset.single_le_sum (f := fun j => (Seams.thrWords k j).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  unfold thrSize; omega

theorem num_le (i : Fin 4) : Seams.thrNums k i ≤ thrSize k := by
  have := Finset.single_le_sum (f := fun j => Seams.thrNums k j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold thrSize; omega

theorem G_le : Fintype.card (Primitive.ThrEq k.P k.Cs k.alg) ≤ thrSize k := num_le k 1
theorem tau_le : Primitive.thrDigits k.P k.Cs k.alg k.den ≤ thrSize k := num_le k 2
theorem M_le : (Primitive.thrOccs k.P k.Cs).length ≤ thrSize k := num_le k 3

theorem W5_le : (PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den))).length ≤
    thrSize k := by
  rw [← thrWords_primes]; exact word_le k 5

theorem len_le_sum : ∀ L : List ℕ, L.length ≤ (L.map (· + 1)).sum
  | [] => le_rfl
  | x :: L => by have := len_le_sum L; simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

theorem Lp_le : (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den)).length ≤ thrSize k := by
  have h := W5_le k
  rw [unaryList_length] at h
  exact (len_le_sum _).trans h

theorem p_le (p : ℕ) (hp : p ∈ SupplierPrime.primesUpTo (Primitive.thrCutoff k.P k.Cs k.alg k.den)) : p ≤ thrSize k := by
  have hm : p ∈ PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den) := by
    rw [PrimThrW.Joins.primesList_sorted, Finset.mem_sort]; exact hp
  have h1 : p + 1 ≤ ((PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den)).map (· + 1)).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hm)
  have h := W5_le k
  rw [unaryList_length] at h
  omega

theorem W6_le : (ListEval.levelWord k.D.M k.D.J k.D.W (ListEval.rowsOf k.D (Primitive.thrOccs k.P k.Cs).length)).length ≤
    thrSize k := by
  rw [← thrWords_level]; exact word_le k 6

theorem DM_le : k.D.M ≤ thrSize k := by
  have h := W6_le k
  unfold ListEval.levelWord ListEval.unary at h
  simp only [List.length_append, List.length_replicate, List.length_singleton] at h
  omega

theorem capOf_le : ListEval.capOf k.D.M k.D.J k.D.W (ListEval.rowsOf k.D (Primitive.thrOccs k.P k.Cs).length)
    (Primitive.thrOccs k.P k.Cs).length ≤ 4 * (thrSize k + thrSize k + 1) := by
  unfold ListEval.capOf
  have := W6_le k
  have := M_le k
  omega

theorem H_le : thrH k.Cs ≤ thrSize k := by
  unfold thrH
  split_ifs with hG
  · exact Nat.zero_le _
  · have ha : k.a ≠ 0 := fun ha => hG (tupleG_zero k.P k.Cs ha)
    have h := word_le k 0
    rw [thrWords_table, if_neg ha, gatesW_len] at h
    have h1 : 1 ≤ (PrimT.ThrTab.tupleG k.Cs).length := List.length_pos_of_ne_nil hG
    have e0 : 2 * (2 * PrimT.tabH (PrimT.ThrTab.tupleG k.Cs) + 1) ≤
        (k.P.n + 1) * (2 * (2 * PrimT.tabH (PrimT.ThrTab.tupleG k.Cs) + 1)) := Nat.le_mul_of_pos_left _ (by omega)
    have e2 := Nat.mul_le_mul_right (1 + (k.P.n + 1) * (2 * (2 * PrimT.tabH (PrimT.ThrTab.tupleG k.Cs) + 1))) h1
    omega

theorem pay_le (i : Fin k.a) : (PrimThrW.TopFront.payOf k.alg (k.Cs i)).length ≤ thrSize k := by
  have hi : i.val < 4 := by have := k.ha; omega
  have h := word_le k ⟨i.val + 1, by omega⟩
  rw [show (⟨i.val + 1, by omega⟩ : Fin 7) = ⟨(⟨i.val, hi⟩ : Fin 4).val + 1, by omega⟩ from rfl, thrWords_pay,
    dif_pos i.isLt] at h
  exact h

theorem digsN_le (p : ℕ) (hp : p ≤ thrSize k) :
    Digs.digsN k.P k.Cs [] k.alg k.den p ≤ 6 * thrSize k := by
  unfold Digs.digsN
  rw [PrimAsm.Records.thrOff_eq]
  have h1 : (∑ i : Fin k.a, (PrimThrW.TopFront.payOf k.alg (k.Cs i)).length) ≤ k.a * thrSize k := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun i : Fin k.a => (PrimThrW.TopFront.payOf k.alg (k.Cs i)).length)
      (thrSize k) (fun i _ => pay_le k i)
    simpa using this
  have h2 : k.a * thrSize k ≤ 4 * thrSize k := Nat.mul_le_mul_right _ k.ha
  have h3 := tau_le k
  simp only [List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero]
  omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
