import Proof.Wire_3_5.Primitive.SeedFix.SWt4

/-! # SWt, part 5: **`swT x hx l : SWParts.SWtT l`**

**`tRun`**: at a SYM request, from the core's blank entry at the capacity `K_t·X^{D_t}`: the SYM front
(`front_runA`), every register cleared (`clearL`), the four slots (`tops_run`, the words by `swt_word`); within
`C_t·X^{D_t'}` steps, every head and register `0`, the residue the front's. **`swT`** packages it as `GuardedWordsMJ` at the SYM guard.

Paper quantity of the main type: the SYM call's framed top tables (`symWords`, kind `1`; P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.SWt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.UnionMachine.NumsA NearCubicWires.SupplierPipeline
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound

section Gate
variable (x : ℕ) (hx : DataDock.DT + 7 ≤ x) (l : Literals)

theorem scan_len {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) :
    2 * natBitLength C.bottomCount + 2 * (List.ofFn C.top).length + 2 ≤ (FinalPass.Out.DataW.scanWord C).length := by
  have hnw : (natWord C.bottomCount).length = 2 * natBitLength C.bottomCount + 1 := by
    have : natWord C.bottomCount = List.replicate (natBitLength C.bottomCount) true ++
      false :: WilliamsPublishedForm.fixedWidthNatBits (natBitLength C.bottomCount) C.bottomCount := rfl
    rw [this]; simp [WilliamsPublishedForm.fixedWidthNatBits]; omega
  unfold FinalPass.Out.DataW.scanWord
  simp only [List.length_append, hnw, frame_len']
  omega

/-- **The top tables' run** at a SYM request. -/
theorem tRun (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩) (σ : St x)
    (hin : σ.st (sIn x) = frame (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩))
    (hsh : ∀ i, σ.sh i = 0) (hbl : ∀ i, i ≠ sIn x → σ.st i = []) (hv : ∀ q, σ.val q = 0) (hc : σ.cell = false) :
    ∃ (τ : St x) (m : ℕ),
      m ≤ CsT l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^
        DsT l F.filterErrDeg ∧
      Step (tM x hx l F) m
        (wenc (KcT l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length +
          1) ^ DkT l F.filterErrDeg) σ).H
        (wenc (KcT l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length +
          1) ^ DkT l F.filterErrDeg) σ).A
        (wenc (KcT l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length +
          1) ^ DkT l F.filterErrDeg) τ).H
        (wenc (KcT l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length +
          1) ^ DkT l F.filterErrDeg) τ).A ∧
      (∀ k : Fin 4, τ.st (sOutT x hx k) = FinalPass.SWParts.swWs l 4 4 (by norm_num) F kclk coef A a ha
        ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ k) ∧
      τ.st (sIn x) = frame (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) ∧
      (∀ i, i ≠ sIn x → (∀ k, i ≠ sOutT x hx k) → (τ.st i).length ≤ CsT l F *
        ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^
          DsT l F.filterErrDeg) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  obtain ⟨X, hXd⟩ : ∃ X, X = (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length +
      1 := ⟨_, rfl⟩
  rw [← hXd]
  have hX1 : 1 ≤ X := by omega
  obtain ⟨cap, hcapd⟩ : ∃ c, c = KcT l F * X ^ DkT l F.filterErrDeg := ⟨_, rfl⟩
  rw [← hcapd]
  have hcapF : FinalPass.SymFront.KF l F * ((fpIn l F kclk coef A a ha
      ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ FinalPass.SymFront.DF l F.filterErrDeg ≤
      cap := by
    rw [← hXd, hcapd]
    exact Nat.mul_le_mul (by unfold KcT; omega) (Nat.pow_le_pow_right hX1 (by unfold DkT; omega))
  obtain ⟨τF, mF, hmF, sF, hO⟩ := FinalPass.SymFront.front_runA x (hx3 x hx) l F kclk coef A a ha ha' Cs carriers
    translation hcall cap hcapF σ ⟨hin, hsh, hbl, hv, hc⟩
  rw [← hXd] at hmF
  obtain ⟨B, hBd⟩ : ∃ B, B = FinalPass.SymFront.CF l F * X ^ FinalPass.SymFront.DFs l F.filterErrDeg := ⟨_, rfl⟩
  have hBc : B ≤ cap := by
    rw [hBd, hcapd]
    exact Nat.mul_le_mul (by unfold KcT; omega) (Nat.pow_le_pow_right hX1 (by unfold DkT; omega))
  have hvle : ∀ q, τF.val q ≤ B := fun q => by have := hO.vle q; rw [← hXd] at this; rw [hBd]; exact this
  have hres : ∀ i, i ≠ sIn x → (τF.st i).length ≤ B := fun i hi => by
    have := hO.resid i hi; rw [← hXd] at this; rw [hBd]; exact this
  obtain ⟨c0, e0, h0⟩ := NumsC.clearL_spec cap B hBc allR τF (fun r _ => hvle r)
  have hlen : allR.length = 512 := by simp [allR]
  rw [hlen] at h0
  obtain ⟨ρ, hρ⟩ : ∃ s, s = NumsC.zeroL τF allR := ⟨_, rfl⟩
  rw [← hρ] at e0
  have ρst : ρ.st = τF.st := by rw [hρ]; rfl
  have ρsh : ρ.sh = τF.sh := by rw [hρ]; rfl
  have ρv : ∀ q, ρ.val q = 0 := fun q => by
    rw [hρ]; show (if q ∈ allR then 0 else τF.val q) = 0; rw [if_pos (show q ∈ allR from List.mem_finRange q)]
  -- the words
  obtain ⟨k, hk⟩ : ∃ k, k = FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers := ⟨_, rfl⟩
  have hS : ∀ j : Fin 4, (∃ (x0 : ℕ) (y rest : List Bool), ρ.st (sS x hx j) = natWord x0 ++ (frame y ++ rest) ∧
      frame (PrimT.S3.topJ k j) = frame y ∧ 2 * natBitLength x0 + 2 * y.length + 2 ≤ cap) ∨
      (ρ.st (sS x hx j) = [] ∧ frame (PrimT.S3.topJ k j) = frame []) := by
    intro j
    by_cases hj : j.val < a'
    · left
      refine ⟨(Cs ⟨j.val, hj⟩).bottomCount, List.ofFn (Cs ⟨j.val, hj⟩).top,
        tabSeg (Stars.symGates (Cs ⟨j.val, hj⟩)), ?_, ?_, ?_⟩
      · rw [ρst]; exact hO.scan j hj
      · rw [hk]; unfold PrimT.S3.topJ
        rw [dif_pos (show j.val < (FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers).a
          from hj)]
        rfl
      · have h1 := scan_len (Cs ⟨j.val, hj⟩)
        have h2 := hres (sS x hx j) (fun e => by
          have := congrArg Fin.val e; rw [sS_val] at this; simp [NumsPh2.sIn_val] at this; omega)
        have h3 : τF.st (sS x hx j) = FinalPass.Out.DataW.scanWord (Cs ⟨j.val, hj⟩) := hO.scan j hj
        rw [h3] at h2
        omega
    · right
      refine ⟨by rw [ρst]; exact hO.scan0 j (by omega), ?_⟩
      rw [hk]; unfold PrimT.S3.topJ
      rw [dif_neg (show ¬ j.val < (FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers).a
        from hj)]
  obtain ⟨c1, e1, h1⟩ := tops_run x hx cap ρ (fun j => frame (PrimT.S3.topJ k j)) hS
    (fun i => by rw [ρsh]; exact hO.heads i)
    (fun j => by rw [ρst]; exact hO.hi ⟨DataDock.DT + 3 + j.val, by have := j.isLt; omega⟩ (by simp))
    (fun i => ρv _)
  have st2 := (WExec.exec cap (WExec.seq e0 e1)).step
  refine ⟨_, _, time_le X cap B c0 c1 mF (KcT l F) (DkT l F.filterErrDeg) (FinalPass.SymFront.CF l F)
    (FinalPass.SymFront.DFs l F.filterErrDeg) hX1 hcapd hBd hBc (by rw [hBd]; exact hmF) h0 h1, Step.seq sF st2,
    fun j => ?_, ?_, fun i hi hk' => ?_, fun i => ?_, fun q => ?_⟩
  · have hw := swt_word l F kclk coef A a ha ha' Cs carriers translation hcall hs j
    rw [hw, ← hk]
    show (((((ρ.sets (sO x hx 0) _).sets (sO x hx 1) _).sets (sO x hx 2) _).sets (sO x hx 3) _).st (sO x hx j)) = _
    fin_cases j <;> simp [Function.update_apply, (sO_inj x hx).ne]
  · have n0 := sO_ne_sIn x hx
    simp [Function.update_of_ne (Ne.symm (n0 0)), Function.update_of_ne (Ne.symm (n0 1)),
      Function.update_of_ne (Ne.symm (n0 2)), Function.update_of_ne (Ne.symm (n0 3)), ρst, hO.hin, hXd]
  · have hk0 : i ≠ sO x hx 0 := hk' 0
    have hk1 : i ≠ sO x hx 1 := hk' 1
    have hk2 : i ≠ sO x hx 2 := hk' 2
    have hk3 : i ≠ sO x hx 3 := hk' 3
    simp only [WState.sets_st]
    rw [Function.update_of_ne hk3, Function.update_of_ne hk2, Function.update_of_ne hk1, Function.update_of_ne hk0,
      ρst]
    have := hres i hi
    have e : CsT l F * X ^ DsT l F.filterErrDeg = (FinalPass.SymFront.CF l F + 10000000 * (KcT l F + 2) ^ 2) *
      X ^ (FinalPass.SymFront.DFs l F.filterErrDeg + 2 * DkT l F.filterErrDeg) := rfl
    have hB2 : B ≤ CsT l F * X ^ DsT l F.filterErrDeg := by
      rw [e, hBd]
      exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hX1 (by omega))
    omega
  · simp only [WState.sets_sh]; rw [ρsh]; exact hO.heads i
  · simp only [WState.sets_val]; exact ρv q

/-- **SWt** (`SWParts.SWtT l`) on the SYM front bank, `x ≥ DT + 7`. -/
noncomputable def swT : FinalPass.SWParts.SWtT l :=
  ⟨LNS x, LNR, _, fun F => tM x hx l F, sIn x, sOutT x hx, fun k => sO_ne_sIn x hx k,
    KcT l, DkT l, CsT l, DsT l,
    fun F kclk coef A a ha r hm σ hin hsh hbl hv hc => by
      obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
      have hm' : mode = .sym := hm
      subst hm'
      exact tRun x hx l F kclk coef A a ha ha' Cs carriers translation hcall σ hin hsh hbl hv hc⟩

end Gate

end NearCubicWires.WireExponent3_5.PrimT.SWt
