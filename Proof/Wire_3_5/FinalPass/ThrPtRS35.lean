import Proof.Wire_3_5.FinalPass.ThrPtRS34

/-! # S2 (THR per point), part 49: the capacities and the step bound from the size

With `needE (thrSize k) ≤ cap`: **`rowCaps_ok`** (every row's `RowCaps`) and **`setupCaps_ok`** (the setup's, the loops'
and the cleanup's capacities); **`cost_ok`**: the run's step bound `thrCost k c u v ≤ boundE (thrSize k)`. Paper
quantity: the per-point evaluator's time `poly(ptSize)` (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.SupplierPipeline

variable (k : Seams.ThrCall) (c : BitInput k.P.n) (u v : k.P.Errors)

theorem RW_need_le (p : ℕ) (hp : p ≤ thrSize k) :
    DigsBody.rowWImpl.need (Digs.digsN k.P k.Cs [] k.alg k.den p) ≤ RWb (thrSize k) := by
  refine (DigsBody.rowWImpl.need_le _).trans ?_
  unfold RWb
  have := digsN_le k p hp
  gcongr

theorem RW_bound_le (p : ℕ) (hp : p ≤ thrSize k) :
    DigsBody.rowWImpl.bound (Digs.digsN k.P k.Cs [] k.alg k.den p) ≤ RWb (thrSize k) := by
  refine (DigsBody.rowWImpl.bound_le _).trans ?_
  unfold RWb
  have := digsN_le k p hp
  gcongr

theorem reps_facts (g : Primitive.ThrEq k.P k.Cs k.alg) (p : ℕ) (sgn : Bool) :
    (repsAt k.P k.Cs k.alg k.den k.D c u v g p sgn).length = Primitive.thrDigits k.P k.Cs k.alg k.den ∧
      ∀ x ∈ repsAt k.P k.Cs k.alg k.den k.D c u v g p sgn, x ≤ thrSize k := by
  refine ⟨by unfold repsAt; rw [tRepL_length], fun x hx => ?_⟩
  unfold repsAt at hx
  exact (tRepL_le _ _ _ _ _ _ _ _ x hx).trans (DM_le k)

theorem coeffs_facts (g : Primitive.ThrEq k.P k.Cs k.alg) (p : ℕ) (hp : 0 < p) (hpU : p ≤ thrSize k) :
    (Term.thrCoeffs k.P k.Cs k.alg g p).length ≤ thrSize k ∧ ∀ x ∈ Term.thrCoeffs k.P k.Cs k.alg g p, x ≤ thrSize k :=
  ⟨by rw [Term.thrCoeffs, List.length_ofFn]; exact M_le k,
    fun x hx => (coeffs_le k.P k.Cs k.alg g p hp x hx).trans hpU⟩

theorem weights_facts (p : ℕ) (hp : 0 < p) (hpU : p ≤ thrSize k) :
    (Term.thrWeights k.P k.Cs k.alg k.den p).length ≤ thrSize k ∧
      ∀ x ∈ Term.thrWeights k.P k.Cs k.alg k.den p, x ≤ thrSize k :=
  ⟨by rw [Term.thrWeights, List.length_ofFn]; exact tau_le k,
    fun x hx => (weights_le k.P k.Cs k.alg k.den p hp x hx).trans hpU⟩

/-- **Every row's capacities.** -/
theorem rowCaps_ok (cap : ℕ) (hcap : needE (thrSize k) ≤ cap) (g : Primitive.ThrEq k.P k.Cs k.alg) (p : ℕ)
    (hp : p ∈ SupplierPrime.primesUpTo (Primitive.thrCutoff k.P k.Cs k.alg k.den)) :
    RowCaps k.P k.Cs k.alg k.den k.D c u v cap g p := by
  have hpU := p_le k p hp
  have hpos : 0 < p := (SupplierPrime.mem_primesUpTo.mp hp).1.pos
  have hr0 := (thrR0_lt k.P k.Cs k.alg g p hpos).le.trans hpU
  obtain ⟨hal, haU⟩ := coeffs_facts k g p hpos hpU
  obtain ⟨hwl, hwU⟩ := weights_facts k p hpos hpU
  obtain ⟨htl, htU⟩ := reps_facts k c u v g p true
  obtain ⟨hsl, hsU⟩ := reps_facts k c u v g p false
  have hτ := tau_le k
  have hM := M_le k
  have hDM := DM_le k
  have e1 := RW_need_le k p hpU
  have e2 := popCap_le p (Term.thrR0 k.P k.Cs k.alg g p) (Primitive.thrOccs k.P k.Cs).length p
    (Primitive.thrDigits k.P k.Cs k.alg k.den) hpU hr0 hM hpU hτ
  have e3 := capOf_le k
  have e4 : 2 * Primitive.thrDigits k.P k.Cs k.alg k.den * (k.D.M + 1) + 2 * (k.D.M + 1) +
      Primitive.thrDigits k.P k.Cs k.alg k.den ≤ 2 * thrSize k * (thrSize k + 1) + 2 * (thrSize k + 1) + thrSize k := by
    gcongr
  have e5 := capT_le p (Term.thrR0 k.P k.Cs k.alg g p) (Primitive.thrOccs k.P k.Cs).length _ _ _ _ hpU hr0 hM hal haU hwl
    hwU (htl.le.trans hτ) htU (hsl.le.trans hτ) hsU
  have e6 := rowWord_le p (Term.thrR0 k.P k.Cs k.alg g p) _ _ hpU hr0 hal haU hwl hwU
  unfold needE at hcap
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The setup's, the loops' and the cleanup's capacities.** -/
theorem setupCaps_ok (cap : ℕ) (hcap : needE (thrSize k) ≤ cap) :
    2 * Primitive.thrDigits k.P k.Cs k.alg k.den + 10 * (Primitive.thrOccs k.P k.Cs).length + 2 * thrH k.Cs + 2 ≤ cap ∧
    2 * k.P.n ≤ cap ∧
    (Primitive.thrOccs k.P k.Cs).length * (1 + (k.P.n + 1) * (2 * (2 * thrH k.Cs + 1))) ≤ cap ∧
    (PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den))).length ≤ cap ∧
    Fintype.card (Primitive.ThrEq k.P k.Cs k.alg) *
      (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den)).length ≤ cap ∧
    Fintype.card (Primitive.ThrEq k.P k.Cs k.alg) + 2 * thrH k.Cs + 8 * (Primitive.thrOccs k.P k.Cs).length +
      Primitive.thrDigits k.P k.Cs k.alg k.den + 1 ≤ cap := by
  have hτ := tau_le k
  have hM := M_le k
  have hH := H_le k
  have hn := n_le k
  have hG := G_le k
  have hW5 := W5_le k
  have hL := Lp_le k
  have e1 : (Primitive.thrOccs k.P k.Cs).length * (1 + (k.P.n + 1) * (2 * (2 * thrH k.Cs + 1))) ≤
      thrSize k * (1 + (thrSize k + 1) * (2 * (2 * thrSize k + 1))) := by gcongr
  have e2 : Fintype.card (Primitive.ThrEq k.P k.Cs k.alg) *
      (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den)).length ≤ thrSize k * thrSize k :=
    Nat.mul_le_mul hG hL
  unfold needE at hcap
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem Crow_le (j p : ℕ) :
    Crow k.P k.Cs k.alg k.den k.D c u v j p ≤ rowE (thrSize k) := by
  unfold Crow
  split_ifs with hj hp
  · have hpU := p_le k p hp
    have hpos : 0 < p := (SupplierPrime.mem_primesUpTo.mp hp).1.pos
    obtain ⟨g, hg⟩ : ∃ g, g = (PrimAsm.Enum.thrEqEquiv k.P k.Cs k.alg).symm ⟨j, hj⟩ := ⟨_, rfl⟩
    rw [← hg, ← rowE_eq]
    have hr0 := (thrR0_lt k.P k.Cs k.alg g p hpos).le.trans hpU
    obtain ⟨hal, haU⟩ := coeffs_facts k g p hpos hpU
    obtain ⟨hwl, hwU⟩ := weights_facts k p hpos hpU
    obtain ⟨htl, htU⟩ := reps_facts k c u v g p true
    obtain ⟨hsl, hsU⟩ := reps_facts k c u v g p false
    exact rowCost_le _ _ _ _ _ _ _ _ _ _ _ _ _ (RW_bound_le k p hpU) hpU hr0 (M_le k) hpU (tau_le k) (DM_le k)
      (capOf_le k) hal haU hwl hwU (htl.trans hsl.symm) (htl.le.trans (tau_le k)) htU hsU
  · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- **The run's step bound is at most `boundE` at the call's size.** -/
theorem cost_ok : thrCost k c u v ≤ boundE (thrSize k) := by
  have hτ := tau_le k
  have hM := M_le k
  have hH := H_le k
  have hn := n_le k
  have hG := G_le k
  have hL := Lp_le k
  have e1 := setupCost_le (Primitive.thrDigits k.P k.Cs k.alg k.den) (Primitive.thrOccs k.P k.Cs).length (thrH k.Cs)
    _ hτ hM hH (cwCost_le (thrH k.Cs) k.P.n (Primitive.thrOccs k.P k.Cs).length hH hn hM)
  have e2 := cleanCost_le (Fintype.card (Primitive.ThrEq k.P k.Cs k.alg)) (Primitive.thrDigits k.P k.Cs k.alg k.den)
    (Primitive.thrOccs k.P k.Cs).length (thrH k.Cs) hG hτ hM hH
  have hPL : ∀ j, primeLoopCost (Crow k.P k.Cs k.alg k.den k.D c u v j)
      (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den)) ≤
      thrSize k * (14 * thrSize k + 13 + rowE (thrSize k)) + 1 := fun j => by
    refine (primeLoopCost_le _ (rowE (thrSize k)) _ (fun p hp =>
      ⟨p_le k p (primesList_mem hp), Crow_le k c u v j p⟩)).trans ?_
    gcongr
  have e3 := gLoopCost_le (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den))
    (Crow k.P k.Cs k.alg k.den k.D c u v) _ (thrSize k) (W5_le k) (Fintype.card (Primitive.ThrEq k.P k.Cs k.alg)) 0
    (fun j _ _ => hPL j)
  have e4 : Fintype.card (Primitive.ThrEq k.P k.Cs k.alg) *
      (thrSize k * (14 * thrSize k + 13 + rowE (thrSize k)) + 1 + 5 * thrSize k + 11) ≤
      thrSize k * (thrSize k * (14 * thrSize k + 13 + rowE (thrSize k)) + 1 + 5 * thrSize k + 11) :=
    Nat.mul_le_mul_right _ hG
  unfold thrCost boundE setupE cleanE
  omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
