import Proof.Wire_3_5.FinalPass.ThrPtRS29

/-! # S2 (THR per point), part 44: the THR per-point evaluator's run (P3:2587-2630, 3170-3178)

`thrProg S R`: the internal program lifted into the per-point layout. `thrCost k c u v`: its step bound.
**`thrCall_run`**: from a `PtIn2` entry at the call's words and numbers, given the rows' capacities (`RowCaps`) and
the setup's, the run meets `PtOut` with the accumulator `rsumThr P Cs alg den (listReportFast D) c u v` — the
per-point sum `Σ_{g,p} R̂_{g,p}(c, u, v)`. Paper quantity: `Σ_{g,p} R̂_{g,p}(c, u, v)` (P3:2587-2630). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline

/-- **The THR per-point program** in the per-point layout. -/
noncomputable def thrProg {ns nr : ℕ} (S : Fin 3 ⊕ Fin 7 ⊕ Fin 7 ↪ Fin (ns + 1))
    (R : Fin 1 ⊕ Fin 4 ⊕ Fin 113 ↪ Fin nr) : WM ns nr :=
  thrInt.liftW (fS S) (fR R)

/-- The run's step bound. -/
noncomputable def thrCost (k : Seams.ThrCall) (c : BitInput k.P.n) (u v : k.P.Errors) : ℕ :=
  setupCost (Primitive.thrDigits k.P k.Cs k.alg k.den) (Primitive.thrOccs k.P k.Cs).length (thrH k.Cs)
      (Corner.cwCost (thrH k.Cs) k.P.n (Primitive.thrOccs k.P k.Cs).length) + 1 +
    (gLoopCost (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den))
        (Crow k.P k.Cs k.alg k.den k.D c u v) 0 (Fintype.card (Primitive.ThrEq k.P k.Cs k.alg)) + 1 +
      cleanCost (Fintype.card (Primitive.ThrEq k.P k.Cs k.alg)) (Primitive.thrDigits k.P k.Cs k.alg k.den)
        (Primitive.thrOccs k.P k.Cs).length (thrH k.Cs))

theorem sOf_pay : ∀ i : Fin 4, sOf (payS i) = .inr (.inl ⟨i.val + 1, by omega⟩) := by decide

theorem primesList_mem {c p : ℕ} (hp : p ∈ PrimThrW.Joins.primesList c) : p ∈ SupplierPrime.primesUpTo c := by
  unfold PrimThrW.Joins.primesList at hp
  rw [List.mem_filter, List.mem_range] at hp
  exact SupplierPrime.mem_primesUpTo.mpr ⟨of_decide_eq_true hp.2, by omega⟩

variable (cap : ℕ)

/-- **The THR per-point evaluator's run.** -/
theorem thrCall_run (k : Seams.ThrCall) {ns nr : ℕ} (S : Fin 3 ⊕ Fin 7 ⊕ Fin 7 ↪ Fin (ns + 1))
    (R : Fin 1 ⊕ Fin 4 ⊕ Fin 113 ↪ Fin nr) (c : BitInput k.P.n) (u v : k.P.Errors) (σ : WState ns nr)
    (hin : Seams.PtIn2 S R c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) (Seams.thrWords k)
      (Seams.thrNums k) σ)
    (hrc : ∀ j (hj : j < gN k.P k.Cs k.alg) p, p ∈ SupplierPrime.primesUpTo (Primitive.thrCutoff k.P k.Cs k.alg k.den) →
      RowCaps k.P k.Cs k.alg k.den k.D c u v cap ((PrimAsm.Enum.thrEqEquiv k.P k.Cs k.alg).symm ⟨j, hj⟩) p)
    (hc1 : 2 * Primitive.thrDigits k.P k.Cs k.alg k.den + 10 * (Primitive.thrOccs k.P k.Cs).length + 2 * thrH k.Cs + 2
      ≤ cap)
    (hcn : 2 * k.P.n ≤ cap)
    (hcK : (Primitive.thrOccs k.P k.Cs).length * (1 + (k.P.n + 1) * (2 * (2 * thrH k.Cs + 1))) ≤ cap)
    (hcL : (PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den))).length ≤ cap)
    (hcG : Fintype.card (Primitive.ThrEq k.P k.Cs k.alg) *
      (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den)).length ≤ cap)
    (hcG2 : Fintype.card (Primitive.ThrEq k.P k.Cs k.alg) + 2 * thrH k.Cs + 8 * (Primitive.thrOccs k.P k.Cs).length +
      Primitive.thrDigits k.P k.Cs k.alg k.den + 1 ≤ cap) :
    ∃ τ', WExec cap (thrProg S R) σ τ' (thrCost k c u v) ∧
      Seams.PtOut S R σ τ' (Seams.rsumThr k.P k.Cs k.alg k.den (ListFast.listReportFast k.D) c u v) := by
  have I := init_of S R k c u v σ hin
  obtain ⟨hmeas, hmz, hGs⟩ := table_facts k
  have hσ3 : (view0 S R σ).st 3 = Seams.thrWords k 0 := (view0_st S R σ 3 (by decide)).trans (hin.1.wd 0)
  have hC : (view0 S R σ).st 0 = frame (List.ofFn c) := (view0_st S R σ 0 (by decide)).trans hin.1.ptC
  have hU : (view0 S R σ).st 1 = frame (List.ofFn (k.P.errorVector k.P.leftBlock u)) :=
    (view0_st S R σ 1 (by decide)).trans hin.1.ptU
  have hV : (view0 S R σ).st 2 = frame (List.ofFn (k.P.errorVector k.P.rightBlock v)) :=
    (view0_st S R σ 2 (by decide)).trans hin.1.ptV
  have h8 : (view0 S R σ).st 8 =
      PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den)) :=
    (view0_st S R σ 8 (by decide)).trans ((hin.1.wd 5).trans (thrWords_primes k))
  have hT5 : ((view0 S R σ).setv 117 (thrH k.Cs)).st 9 =
      ListEval.levelWord k.D.M k.D.J k.D.W (ListEval.rowsOf k.D (Primitive.thrOccs k.P k.Cs).length) :=
    (view0_st S R σ 9 (by decide)).trans ((hin.1.wd 6).trans (thrWords_level k))
  have hpay : ∀ i : Fin 4, ((view0 S R σ).setv 117 (thrH k.Cs)).st (payS i) =
      if h : i.val < k.a then PrimThrW.TopFront.payOf k.alg (k.Cs ⟨i.val, h⟩) else [] := fun i => by
    show (view0 S R σ).st (payS i) = _
    rw [view0_st S R σ (payS i) (payS_lt i), sOf_pay i, hin.1.wd, thrWords_pay]
  have hB := baseOK_of (view0 S R σ) k.a _ _ _ I (thrH k.Cs)
  have hrow : ∀ j < Fintype.card (Primitive.ThrEq k.P k.Cs k.alg),
      ∀ p ∈ PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den),
      RowStepOK cap ((view0 S R σ).setv 117 (thrH k.Cs)) (Primitive.thrOccs k.P k.Cs).length
        (Primitive.thrDigits k.P k.Cs k.alg k.den)
        (Pop.cornerWord ((PrimT.ThrTab.tupleG k.Cs).map NormalizedThresholdGate.eval) c
          (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v)) j
        (rowVal k.P k.Cs k.alg k.den k.D c u v j p) (Crow k.P k.Cs k.alg k.den k.D c u v j p) p := by
    intro j hj p hp
    have hj' : j < gN k.P k.Cs k.alg := by rw [← card_thrEq]; exact hj
    have hp' := primesList_mem hp
    have h := rows_ok k.P k.Cs k.alg k.den k.D c u v cap k.ha _ hB hpay hT5 j hj' p hp' (hrc j hj' p hp')
    rwa [occCorners_eq] at h
  obtain ⟨τf, e, hv, hsh, hcell, hst, hsc'⟩ := thrInt_spec cap (view0 S R σ) k.a _ _ _ (thrH k.Cs) I
    (PrimT.ThrTab.tupleG k.Cs) c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v)
    (fun i hi => by rw [hσ3]; exact hmeas i hi) (by rw [hσ3]; exact hmz) (fun ha => hσ3.trans (hGs ha))
    (tupleG_zero k.P k.Cs) (tupleG_len k.P k.Cs) hC hU hV (thrH_hov k.Cs)
    (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den)) h8
    (fun p hp => (SupplierPrime.mem_primesUpTo.mp (primesList_mem hp)).1.pos)
    (rowVal k.P k.Cs k.alg k.den k.D c u v) (Crow k.P k.Cs k.alg k.den k.D c u v)
    (rowVal_le k.P k.Cs k.alg k.den k.D c u v) hrow hc1 hcn hcK hcL hcG hcG2
  obtain ⟨τ', e', hout⟩ := transport S R cap thrInt σ hin.1.sc _ _ τf e hv hsh hcell hst hsc'
  refine ⟨τ', e', ?_⟩
  rw [rsum_loops]
  exact hout

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
