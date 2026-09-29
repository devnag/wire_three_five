import Proof.Wire_3_5.FinalPass.SdCtr5

/-! # S4 (the seeds phase), part 15: the evaluators at every center and pair (P3:3170-3178)

The center loop takes the evaluator as a hypothesis from any state meeting `PtEnvC` (part 12). Here it is discharged
per mode, from the center loop's entry state `ωR0` carrying the call's words and numbers: **`evC_thr`** (S2's
`thrPtProg`: the mode word `13`, the primes' list, starts with `1` since the cutoff is at least `563`,
`thr_mode_bit`) and **`evC_sym`** (the SYM evaluator `E`: word `13` blank). Each builds the evaluator's `PtIn2` from
`PtEnvC` and the entry state's words, numbers, blank scratch and cell.

Paper quantity of the main type: the per-point sums `Σ R̂` (S2's `rsumThr`, S3's `rsumSym`) at every sampled point. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 ThrCall SymCall thrWords thrNums rsumThr rsumSym
  PtIn PtIn2)

/-! ## The mode bit -/

theorem primesList_head (c : ℕ) (hc : 2 ≤ c) : ∃ t, PrimThrW.Joins.primesList c = 2 :: t := by
  unfold PrimThrW.Joins.primesList
  rw [show c + 1 = 3 + (c - 2) by omega, List.range_add, List.filter_append]
  have h3 : (List.range 3).filter (fun p => decide (Nat.Prime p)) = [2] := by decide
  rw [h3]
  exact ⟨_, rfl⟩

/-- **THR's word `13` reads `1` at its start** (the primes' list starts with `2`). -/
theorem thr_mode_bit (k : ThrCall) : readTapeBit (thrWords k 5) 0 = true := by
  have hw : thrWords k 5 = PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (thrCutoff k.P k.Cs k.alg k.den)) := by
    simp [thrWords]
  obtain ⟨t, ht⟩ := primesList_head (thrCutoff k.P k.Cs k.alg k.den)
    (le_trans (by norm_num) (SupplierPrime.canonicalPrimeCutoff_ge_563 _ _))
  rw [hw, ht]
  rfl

section Lay
variable {nw nn nsc nrs : ℕ}

theorem kept_word (i : ℕ) (hi : i < 17) :
    KeptC (bst (30 + i) (by omega) : Fin (bns nw nsc + 1)) :=
  ⟨kept_bst (30 + i) _ (by omega) (by omega) (by omega) (by omega) (by omega),
    by simp only [tC]; apply bst_ne; omega, by simp only [tRow]; apply bst_ne; omega,
    by simp only [tCol]; apply bst_ne; omega⟩

end Lay

variable (E : SymPtEval2)

/-- **The THR evaluator at every center and pair.** -/
theorem evC_thr (cap : ℕ) (k : ThrCall) {N : ℕ} (eqv : k.P.Errors ≃ Fin N) (ωR0 : BS E.nw E.nn E.nsc E.nrs)
    (hw : ∀ i : Fin 7, ωR0.st (bst (38 + i.val) (by omega)) = thrWords k i)
    (hn : ∀ i : Fin 4, ωR0.val (brg (1 + i.val) (by omega)) = thrNums k i)
    (hz : ∀ j : Fin 113, ωR0.val (brg (5 + j.val) (by omega)) = 0) (hacc : ωR0.val rAcc = 0)
    (hsh : ∀ i, ωR0.sh i = 0) (hcell : ωR0.cell = false)
    (hneed : ThrPt.thrPtProg.need (k.P.n + (∑ i, (thrWords k i).length) + ∑ i, thrNums k i) ≤ cap) :
    ∀ (c : BitInput k.P.n) (a b : Fin N) (ω₀ : BS E.nw E.nn E.nsc E.nrs),
      PtEnvC c (k.P.errorVector k.P.leftBlock (eqv.symm a)) (k.P.errorVector k.P.rightBlock (eqv.symm b)) ωR0 ω₀ →
      ∃ ω₁, WExec cap (evalD E) ω₀ ω₁ (ThrPt.thrPtProg.bound (k.P.n + (∑ i, (thrWords k i).length) +
          ∑ i, thrNums k i) + 1) ∧
        EvOut (rsumThr k.P k.Cs k.alg k.den (ListFast.listReportFast k.D) c (eqv.symm a) (eqv.symm b)) ω₀ ω₁ := by
  intro c a b ω₀ hP
  have hfl : ∀ (j : ℕ) (hj : j < 220), j ≠ 118 → j ≠ 119 → j ≠ 165 → j ≠ 195 → j ≠ 198 →
      ω₀.val (brg j hj) = ωR0.val (brg j hj) := fun j hj h1 h2 h3 h4 h5 =>
    hP.val _ (by simp only [rgX]; apply brg_ne; omega) (by simp only [rM]; apply brg_ne; simp; omega)
      (by simp only [rM]; apply brg_ne; simp; omega) (by simp only [cF]; apply brg_ne; simp; omega)
      (by simp only [cF]; apply brg_ne; simp; omega)
  have hsh0 : ∀ i, i ≠ tI → ω₀.sh i = 0 := fun i hi => by rw [hP.sh i hi]; exact hsh i
  have hin : PtIn2 STe RTe c (k.P.errorVector k.P.leftBlock (eqv.symm a))
      (k.P.errorVector k.P.rightBlock (eqv.symm b)) (thrWords k) (thrNums k) ω₀ := by
    refine ⟨⟨hP.C, hP.U, hP.V, fun i => ?_, fun j b hb => hP.sc _ ?_ b hb, fun x => ?_, fun i => ?_, ?_, fun j => ?_⟩, ?_⟩
    · have := i.isLt
      show ω₀.st (bst (38 + i.val) (by omega)) = _
      rw [show (bst (38 + i.val) (by omega) : Fin (bns E.nw E.nsc + 1)) = bst (30 + (8 + i.val)) (by omega) from
        Fin.ext (by simp [bst]; omega), hP.st _ (kept_word (8 + i.val) (by omega)),
        show (bst (30 + (8 + i.val)) (by omega) : Fin (bns E.nw E.nsc + 1)) = bst (38 + i.val) (by omega) from
        Fin.ext (by simp [bst]; omega)]
      exact hw i
    · have := j.isLt
      show IsSc (bst (18 + j.val) (by omega))
      simp only [IsSc, bst]
      omega
    · apply hsh0
      rcases x with i | i | i
      · have := i.isLt; show bst (1 + i.val) (by omega) ≠ tI; simp only [tI]; apply bst_ne; omega
      · have := i.isLt; show bst (38 + i.val) (by omega) ≠ tI; simp only [tI]; apply bst_ne; omega
      · have := i.isLt; show bst (18 + i.val) (by omega) ≠ tI; simp only [tI]; apply bst_ne; omega
    · have := i.isLt
      show ω₀.val (brg (1 + i.val) (by omega)) = _
      rw [hfl _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hn i
    · show ω₀.val (brg 0 (by omega)) = 0
      rw [hfl _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hacc
    · have := j.isLt
      show ω₀.val (brg (5 + j.val) (by omega)) = 0
      rw [hfl _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hz j
    · rw [hP.cell]; exact hcell
  have hbit : wbit ω₀ tM = true := by
    unfold wbit
    rw [hsh0 tM (by simp only [tM, tI]; apply bst_ne; omega),
      show (tM : Fin (bns E.nw E.nsc + 1)) = bst (30 + 13) (by omega) from rfl,
      hP.st _ (kept_word 13 (by omega)),
      show (bst (30 + 13) (by omega) : Fin (bns E.nw E.nsc + 1)) = bst (38 + (5 : Fin 7).val) (by omega) from rfl,
      hw 5]
    exact thr_mode_bit k
  have hsc : ∀ i, IsSc i → ∀ b ∈ ω₀.st i, b = false := hP.sc
  exact evalT_spec E cap k c (eqv.symm a) (eqv.symm b) ω₀ hbit hin hsc hneed

/-- **The SYM evaluator at every center and pair.** -/
theorem evC_sym (cap : ℕ) (k : SymCall) {N : ℕ} (eqv : k.P.Errors ≃ Fin N) (ωR0 : BS E.nw E.nn E.nsc E.nrs)
    (hw : ∀ i : Fin E.nw, ωR0.st (SSe (.inr (.inl i))) = E.words k i)
    (h13 : ωR0.st (bst (30 + 13) (by omega)) = [])
    (hn : ∀ i : Fin E.nn, ωR0.val (RSe (.inr (.inl i))) = E.nums k i)
    (hz : ∀ j : Fin E.nrs, ωR0.val (RSe (.inr (.inr j))) = 0) (hacc : ωR0.val rAcc = 0)
    (hsh : ∀ i, ωR0.sh i = 0) (hcell : ωR0.cell = false)
    (hneed : E.need (k.P.n + (∑ i, (E.words k i).length) + ∑ i, E.nums k i) ≤ cap) :
    ∀ (c : BitInput k.P.n) (a b : Fin N) (ω₀ : BS E.nw E.nn E.nsc E.nrs),
      PtEnvC c (k.P.errorVector k.P.leftBlock (eqv.symm a)) (k.P.errorVector k.P.rightBlock (eqv.symm b)) ωR0 ω₀ →
      ∃ ω₁, WExec cap (evalD E) ω₀ ω₁ (E.bound (k.P.n + (∑ i, (E.words k i).length) + ∑ i, E.nums k i) + 1) ∧
        EvOut (rsumSym k.P k.Cs k.Pl c (eqv.symm a) (eqv.symm b)) ω₀ ω₁ := by
  intro c a b ω₀ hP
  have hlo : ∀ q : Fin (bnr E.nn E.nrs), 220 ≤ q.val → ω₀.val q = ωR0.val q := fun q hq =>
    hP.val q (fun h => by rw [h] at hq; simp [rgX, brg] at hq <;> omega)
      (fun h => by rw [h] at hq; simp [rM, brg] at hq <;> omega)
      (fun h => by rw [h] at hq; simp [rM, brg] at hq <;> omega)
      (fun h => by rw [h] at hq; simp [cF, brg] at hq <;> omega)
      (fun h => by rw [h] at hq; simp [cF, brg] at hq <;> omega)
  have hsh0 : ∀ i, i ≠ tI → ω₀.sh i = 0 := fun i hi => by rw [hP.sh i hi]; exact hsh i
  have hwk : ∀ i : Fin E.nw, KeptC (SSe (.inr (.inl i)) : Fin (bns E.nw E.nsc + 1)) := fun i => by
    have := i.isLt
    have hv : (SSe (.inr (.inl i)) : Fin (bns E.nw E.nsc + 1)).val = 46 + i.val := rfl
    have hne : ∀ (j : ℕ) (hj : j < 47), j < 40 → (SSe (.inr (.inl i)) : Fin (bns E.nw E.nsc + 1)) ≠ bst j hj :=
      fun j hj h40 h => by
        have e := congrArg Fin.val h
        rw [hv] at e
        simp only [bst] at e
        omega
    exact ⟨⟨hne 0 _ (by omega), hne 2 _ (by omega), hne 3 _ (by omega),
      fun k => by
        have := k.isLt
        exact ⟨hne _ _ (by omega), hne _ _ (by omega), hne _ _ (by omega)⟩,
      by simp only [IsSc, hv]; omega⟩, hne 1 _ (by omega), hne 25 _ (by omega), hne 26 _ (by omega)⟩
  have hin : PtIn2 SSe RSe c (k.P.errorVector k.P.leftBlock (eqv.symm a))
      (k.P.errorVector k.P.rightBlock (eqv.symm b)) (E.words k) (E.nums k) ω₀ := by
    refine ⟨⟨hP.C, hP.U, hP.V, fun i => ?_, fun j b hb => hP.sc _ ?_ b hb, fun x => ?_, fun i => ?_, ?_, fun j => ?_⟩, ?_⟩
    · rw [hP.st _ (hwk i)]; exact hw i
    · show IsSc (⟨47 + E.nw + j.val, _⟩ : Fin (bns E.nw E.nsc + 1))
      simp only [IsSc]
      omega
    · apply hsh0
      intro h
      have e := congrArg Fin.val h
      rcases x with i | i | i
      · have := i.isLt; simp [SSe, sSv, tI, bst] at e; omega
      · have := i.isLt; simp [SSe, sSv, tI, bst] at e; omega
      · have := i.isLt; simp [SSe, sSv, tI, bst] at e; omega
    · rw [hlo _ (by show 220 ≤ 220 + i.val; omega)]; exact hn i
    · show ω₀.val (⟨0, _⟩ : Fin (bnr E.nn E.nrs)) = 0
      rw [show (⟨0, by unfold bnr; omega⟩ : Fin (bnr E.nn E.nrs)) = rAcc from rfl,
        hP.val _ (by simp only [rAcc, rgX]; apply brg_ne; omega) (by simp only [rAcc, rM]; apply brg_ne; simp)
          (by simp only [rAcc, rM]; apply brg_ne; simp) (by simp only [rAcc, cF]; apply brg_ne; simp)
          (by simp only [rAcc, cF]; apply brg_ne; simp)]
      exact hacc
    · rw [hlo _ (by show 220 ≤ 220 + E.nn + j.val; omega)]; exact hz j
    · rw [hP.cell]; exact hcell
  have hbit : wbit ω₀ tM = false := by
    unfold wbit
    rw [hsh0 tM (by simp only [tM, tI]; apply bst_ne; omega),
      show (tM : Fin (bns E.nw E.nsc + 1)) = bst (30 + 13) (by omega) from rfl,
      hP.st _ (kept_word 13 (by omega)), h13]
    rfl
  exact evalS_spec E cap k c (eqv.symm a) (eqv.symm b) ω₀ hbit hin hP.sc hneed

end NearCubicWires.WireExponent3_5.FinalPass.Sd
