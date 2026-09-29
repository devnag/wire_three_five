import Proof.Wire_3_5.UnionMachine.FrontCostSUE

/-! # C6 front, the finish (F6): the fronts at the gate (P3:3669-3697)

**`frontsFWE3`** : `∀ l, Σ e, ∀ F, GateFreeOK l F → PlanW3.FrontsFWE3 e l F` — residual U0–U5 with the atom test, the
`fronts` argument of `PlanW3.union_planW3`. At margin `e := costDeg l + 1` (the front's polynomial degree, a function of
the literals only), for every coefficient, source work, primitive and language: C1's degree `dS`, the time factor
`K_f = KfC + KfT`, and at every `N₀` the front (**`frontAtS`**): the machine `FrontTop.topM` on `tfS` tapes, the reference
output `FrontOutRef.outRef` at the capacities `capQ`, `RQ`, `RQ + 1`, the onset past `N₀` and the thresholds of
`topFacts_ev`, `cost_ev` and `outRef_fields`, and the cost `2N + 6` below the onset, `K_f(q+1)^7(callBudget q + β(q))`
past it (**`run_S`**: `top_run` enlarged by `cost_ev`).

Paper quantity of the main type: the front's output bank, decision, capacities and time (`FrontAtW3`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFinish
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW NearCubicWires.WireExponent3_5.UnionMachine.PlanW2
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (BU)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTopS
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCostSUE (costDeg KfT)

/-- The front's margin degree bound holds at `e = costDeg l + 1`. -/
theorem hdegS (l : Literals) : costDeg l + 1 ≤ kE l (costDeg l + 1) := by unfold kE; omega

/-- The pinned threshold is nonnegative. -/
theorem thr_nonneg (l : Literals) : 0 ≤ (gateParams1 l).threshold := by
  have h1 := (gateParams1 l).thresholdAboveMidpoint
  have h2 := (gateParams1 l).sp_nonneg
  have h3 := (gateParams1 l).roundingReserve
  have h4 : (0 : ℝ) ≤ 5 * Real.sqrt (24 * ((gateParams1 l).v0 : ℝ)) := by positivity
  have h5 : (0 : ℝ) ≤ ((gateParams1 l).eps0 : ℝ) := by exact_mod_cast (gateParams1 l).eps0_nonneg
  have h6 : (0 : ℝ) ≤ ((gateParams1 l).threshold : ℝ) := by linarith
  exact_mod_cast h6

section SUE
variable (l : Literals) (F : GateFree l) (e coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L)

/-- The front's tape count: phase 1, phase 2, both chains. -/
noncomputable def tfS (c : Plan.C1At (dS l F e coef A L hL)) : ℕ :=
  1 + FrontPh1.PH1 (kE l e) + FrontPh2.PH2 (gateSource l) (gatePCPP l) (kE l e) +
    (FrontRest.RS Mode.thr (DwS l F e coef A L hL) (IUE l F e coef A).descDeg (IUE l F e coef A).carrierDeg
      (DeS l F e coef A) (DtS l F e coef A L hL) c +
    FrontRest.RS Mode.sym (DwS l F e coef A L hL) (IUE l F e coef A).descDeg (IUE l F e coef A).carrierDeg
      (DeS l F e coef A) (DtS l F e coef A L hL) c)

theorem tf_one (c : Plan.C1At (dS l F e coef A L hL)) : 1 ≤ tfS l F e coef A L hL c := by unfold tfS; omega

theorem tf_p1 (c : Plan.C1At (dS l F e coef A L hL)) : 1 + FrontPh1.PH1 (kE l e) ≤ tfS l F e coef A L hL c := by
  unfold tfS; omega

theorem tf_p2 (c : Plan.C1At (dS l F e coef A L hL)) :
    1 + FrontPh1.PH1 (kE l e) + FrontPh2.PH2 (gateSource l) (gatePCPP l) (kE l e) ≤ tfS l F e coef A L hL c := by
  unfold tfS; omega

theorem tf_r (c : Plan.C1At (dS l F e coef A L hL)) : ∀ m : Mode,
    1 + FrontPh1.PH1 (kE l e) + FrontPh2.PH2 (gateSource l) (gatePCPP l) (kE l e) +
      FrontRest.RS m (DwS l F e coef A L hL) (IUE l F e coef A).descDeg (IUE l F e coef A).carrierDeg
        (DeS l F e coef A) (DtS l F e coef A L hL) c ≤ tfS l F e coef A L hL c := by
  intro m; cases m <;> unfold tfS <;> omega

/-- **The front's machine** at onset `C`. -/
noncomputable def topS (c : Plan.C1At (dS l F e coef A L hL)) (P : FusedPrimitive (IUE l F e coef A)) (C : ℕ) :=
  FrontTop.topM P (tfS l F e coef A L hL c) (tf_one l F e coef A L hL c) (gateSource l) (gatePCPP l) (kE l e)
    (gateApad l) (recOracleDeg l) (DwS l F e coef A L hL) (IUE l F e coef A).descDeg (IUE l F e coef A).carrierDeg
    (DeS l F e coef A) (DtS l F e coef A L hL) c (tf_p1 l F e coef A L hL c) (tf_p2 l F e coef A L hL c)
    (tf_r l F e coef A L hL c) C (FrontSemSUE.hhOf l e L hL) (cpadOf (FrontSemSUE.hhOf l e L hL))
    (KwS l F e coef A L hL) (KbS l F e coef A L hL) (DbS l F e coef A L hL) true (gateCParams1 l).ζ (gateCδ1 l)
    (CeS l F e coef A) (CtS l F e coef A L hL) F.cr
    (FrontPw.pwW (KbS l F e coef A L hL) (DbS l F e coef A L hL) true (gateCParams1 l).ζ (gateCδ1 l) (aVS l) (bVS l)
      (aTS l) (bTS l)) F.cr (32 * coef + 1) (gate0 l F).E.Amain

/-- **The front's onset**: past `N₀`, `topFacts_ev`, `cost_ev` and `outRef_fields`. -/
noncomputable def onS (hcoef : 1 ≤ coef) (P : FusedPrimitive (IUE l F e coef A)) (hdeg : costDeg l + 1 ≤ kE l e)
    (c : Plan.C1At (dS l F e coef A L hL)) (N₀ : ℕ) : ℕ :=
  max N₀ (max (Classical.choose (topFacts_ev l F e coef A L hL c))
    (max (Classical.choose (FrontCostSUE.cost_ev l F e coef A L hL hcoef hdeg c))
      (Classical.choose (FrontCaps.outRef_fields l F e coef A L hL hcoef P (FrontCaps.gridFacts_SUE l F e coef A L hL)))))

/-- **The front's cost**: `2N + 6` below the onset, `K_f(q+1)^7(callBudget q + β(q))` past it. -/
noncomputable def costS (c : Plan.C1At (dS l F e coef A L hL)) (on Kf N : ℕ) : ℕ :=
  if N < on then 2 * N + 6 else
    Kf * ((BU l F e coef A).q N + 1) ^ (callDegMargin - 1) *
      ((BU l F e coef A).callBudget ((BU l F e coef A).q N) + c.budgetAt (BU l F e coef A) ((BU l F e coef A).q N))

/-- **The front's run** at every input and witness: `top_run` enlarged to the cost. -/
theorem run_S (hcoef : 1 ≤ coef) (P : FusedPrimitive (IUE l F e coef A)) (hdeg : costDeg l + 1 ≤ kE l e)
    (c : Plan.C1At (dS l F e coef A L hL)) (N₀ N : ℕ) (x : BitInput N) (w : List Bool) (hw : w.length = N / 16) :
    ∃ (Hf : Fin (NW P (tfS l F e coef A L hL c)) → ℕ) (Af' : Fin (NW P (tfS l F e coef A L hL c)) → List Bool),
      Step (topS l F e coef A L hL c P (onS l F e coef A L hL hcoef P hdeg c N₀))
        (costS l F e coef A L hL c (onS l F e coef A L hL hcoef P hdeg c N₀) (FrontCaps.KfC l F + KfT l F) N)
        (fun _ => 0) (entryA x w) Hf Af' ∧
      (∀ i, Hf (lp P (tfS l F e coef A L hL c) i) = bankH P ((FrontOutRef.outRef (SUE l F e coef A L hL)
        (FrontCaps.gridFacts_SUE l F e coef A L hL) (onS l F e coef A L hL hcoef P hdeg c N₀)
        (fun N => FrontCaps.capQ l F e coef A ((BU l F e coef A).q N))
        (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N))
        (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1) N x w).kept P) i) ∧
      (∀ i, Af' (lp P (tfS l F e coef A L hL c) i) = bankA P
        (FrontOutRef.outRef (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
          (onS l F e coef A L hL hcoef P hdeg c N₀) (fun N => FrontCaps.capQ l F e coef A ((BU l F e coef A).q N))
          (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N))
          (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1) N x w).cap
        (FrontOutRef.outRef (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
          (onS l F e coef A L hL hcoef P hdeg c N₀) (fun N => FrontCaps.capQ l F e coef A ((BU l F e coef A).q N))
          (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N))
          (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1) N x w).R
        (FrontOutRef.outRef (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
          (onS l F e coef A L hL hcoef P hdeg c N₀) (fun N => FrontCaps.capQ l F e coef A ((BU l F e coef A).q N))
          (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N))
          (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1) N x w).Lg
        ((FrontOutRef.outRef (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
          (onS l F e coef A L hL hcoef P hdeg c N₀) (fun N => FrontCaps.capQ l F e coef A ((BU l F e coef A).q N))
          (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N))
          (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1) N x w).kept P) i) := by
  have hon1 : Classical.choose (topFacts_ev l F e coef A L hL c) ≤ onS l F e coef A L hL hcoef P hdeg c N₀ := by
    unfold onS; omega
  have hon2 : Classical.choose (FrontCostSUE.cost_ev l F e coef A L hL hcoef hdeg c) ≤
      onS l F e coef A L hL hcoef P hdeg c N₀ := by
    unfold onS; omega
  have hv0 : (SUE l F e coef A L hL).params.v0 = (aVS l : ℚ) / bVS l := by
    rw [FrontSemSUE.sue_v0]; exact num_div_den _ (gateParams1 l).v0_pos.le
  have hτ : (SUE l F e coef A L hL).params.threshold = (aTS l : ℚ) / bTS l := by
    rw [FrontSemSUE.sue_thr]; exact num_div_den _ (thr_nonneg l)
  obtain ⟨Hf, Af', s, h1, h2⟩ := FrontSemRun.top_run P (tfS l F e coef A L hL c) (tf_one l F e coef A L hL c)
    (gateSource l) (gatePCPP l) (kE l e) (gateApad l) (recOracleDeg l) (DwS l F e coef A L hL) (DeS l F e coef A)
    (DtS l F e coef A L hL) c (tf_p1 l F e coef A L hL c) (tf_p2 l F e coef A L hL c) (tf_r l F e coef A L hL c)
    (onS l F e coef A L hL hcoef P hdeg c N₀) (FrontSemSUE.hhOf l e L hL) (cpadOf (FrontSemSUE.hhOf l e L hL))
    (le_max_right _ _) (KwS l F e coef A L hL) (gateZeta_pos l) (gateZeta_lt l) (KbS l F e coef A L hL)
    (DbS l F e coef A L hL) (gateCδ1 l) (CeS l F e coef A) (CtS l F e coef A L hL) F.cr
    (MSS l F e coef A L hL ((SUE l F e coef A L hL).pcp.nativeWidth N)) (aVS l) (bVS l) (aTS l) (bTS l) F.cr
    (32 * coef + 1) (gate0 l F).E.Amain (FrontSemSUE.sue_parity l F e coef A L hL)
    (FrontSemSUE.sue_const l F e coef A L hL) (by show 2 ≤ 2; exact le_rfl) (by show 4 ≤ 26; omega)
    (FrontCaps.gridFacts_SUE l F e coef A L hL) (FrontSemSUE.sue_gridSize l F e coef A L hL)
    (FrontSemSUE.sue_gridMass l F e coef A L hL) (Rat.den_pos _) (Rat.den_pos _) hv0 hτ (fun _ => rfl)
    (FrontSemSUE.sue_G l F e coef A L hL) (fun N => FrontCaps.capQ l F e coef A ((BU l F e coef A).q N))
    (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N))
    (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1) x w hw
    (fun hCN => Classical.choose_spec (topFacts_ev l F e coef A L hL c) N (le_trans hon1 hCN))
  refine ⟨Hf, Af', Step.enlarge s ?_, h1, h2⟩
  unfold costS
  split_ifs with hN
  · unfold FrontSemRun.costOf
    rw [if_pos hN]
  · have hc := Classical.choose_spec (FrontCostSUE.cost_ev l F e coef A L hL hcoef hdeg c) N (by omega)
      (onS l F e coef A L hL hcoef P hdeg c N₀) (by omega) x w hw
    refine hc.trans ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

/-- **The front at the pinned setup** (residual U0–U5 with the atom test): `K_f = KfC + KfT`, `A_f = 8`. -/
noncomputable def frontAtS (hcoef : 1 ≤ coef) (P : FusedPrimitive (IUE l F e coef A)) (hdeg : costDeg l + 1 ≤ kE l e)
    (c : Plan.C1At (dS l F e coef A L hL)) (N₀ : ℕ) :
    PlanW3.FrontAtW3 P (SUE l F e coef A L hL) c 8 (FrontCaps.KfC l F + KfT l F) N₀ where
  tf := tfS l F e coef A L hL c
  sf := _
  M := topS l F e coef A L hL c P (onS l F e coef A L hL hcoef P hdeg c N₀)
  cost := costS l F e coef A L hL c (onS l F e coef A L hL hcoef P hdeg c N₀) (FrontCaps.KfC l F + KfT l F)
  onset := onS l F e coef A L hL hcoef P hdeg c N₀
  honset := le_max_left _ _
  callOk := FrontOutRef.callOkI (I := IUE l F e coef A)
  hok := fun _ _ _ _ r _ => FrontOutRef.callOkI_iff r
  out := FrontOutRef.outRef (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
    (onS l F e coef A L hL hcoef P hdeg c N₀) (fun N => FrontCaps.capQ l F e coef A ((BU l F e coef A).q N))
    (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N))
    (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1)
  run := fun N x w hw => run_S l F e coef A L hL hcoef P hdeg c N₀ N x w hw
  loop := (Classical.choose_spec (FrontCaps.outRef_fields l F e coef A L hL hcoef P
    (FrontCaps.gridFacts_SUE l F e coef A L hL)) (onS l F e coef A L hL hcoef P hdeg c N₀) (by unfold onS; omega)).1
  capPos := fun N x w _ => FrontOutRef.outRef_capPos (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
    _ _ _ _ (fun N => FrontCaps.capQ_pos l F e coef A _) N x w
  accFit := (Classical.choose_spec (FrontCaps.outRef_fields l F e coef A L hL hcoef P
    (FrontCaps.gridFacts_SUE l F e coef A L hL)) (onS l F e coef A L hL hcoef P hdeg c N₀) (by unfold onS; omega)).2.1
  sem := fun N x w hw => FrontOutRef.outRef_sem P (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
    _ _ _ _ N x w hw
  rej := fun N x w _ hN => FrontOutRef.outRef_rej (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
    _ _ _ _ N x w hN
  costRej := fun N _ hN => by
    show costS l F e coef A L hL c (onS l F e coef A L hL hcoef P hdeg c N₀) (FrontCaps.KfC l F + KfT l F) N ≤
      8 * (N + 1) ^ aE l e
    unfold costS
    rw [if_pos hN]
    have h1 : N + 1 ≤ (N + 1) ^ aE l e := Nat.le_self_pow (by unfold aE; omega) _
    omega
  costAcc := fun N _ hN => by
    unfold costS
    rw [if_neg (by omega)]
    exact Nat.le_add_left _ _
  len := fun N x w _ _ hne => FrontOutRef.outRef_len (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
    _ _ _ _ N x w hne
  perCall := fun N x w hw hN hne =>
    ((Classical.choose_spec (FrontCaps.outRef_fields l F e coef A L hL hcoef P
      (FrontCaps.gridFacts_SUE l F e coef A L hL)) (onS l F e coef A L hL hcoef P hdeg c N₀)
        (by unfold onS; omega)).2.2.1 N x w hw hN hne).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  capAcc := fun N x w hw hN =>
    ((Classical.choose_spec (FrontCaps.outRef_fields l F e coef A L hL hcoef P
      (FrontCaps.gridFacts_SUE l F e coef A L hL)) (onS l F e coef A L hL hcoef P hdeg c N₀)
        (by unfold onS; omega)).2.2.2 N x w hw hN).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))

end SUE

/-- **The fronts at one literal set and gate**, at margin `costDeg l + 1`. -/
noncomputable def frontsS (l : Literals) (F : GateFree l) : PlanW3.FrontsFWE3 (costDeg l + 1) l F :=
  ⟨8, fun coef hcoef A P L hL => ⟨dS l F (costDeg l + 1) coef A L hL, fun c =>
    ⟨FrontCaps.KfC l F + KfT l F, fun N₀ => frontAtS l F (costDeg l + 1) coef A L hL hcoef P (hdegS l) c N₀⟩⟩⟩

/-- **The fronts finish** (residual U0–U5 with the atom test): `PlanW3.union_planW3`'s `fronts`. -/
noncomputable def frontsFWE3 : ∀ l : Literals, Σ e : ℕ, ∀ F : GateFree l, GateFreeOK l F → PlanW3.FrontsFWE3 e l F :=
  fun l => ⟨costDeg l + 1, fun F _ => frontsS l F⟩


end NearCubicWires.WireExponent3_5.UnionMachine.FrontFinish
