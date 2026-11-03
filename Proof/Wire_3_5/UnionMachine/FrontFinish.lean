import Lean
import Proof.Wire_3_5.UnionMachine.FrontCostSUE
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.FrontCaps
import Proof.Wire_3_5.UnionMachine.FrontOutRef
import Proof.Wire_3_5.UnionMachine.FrontSemRun
import Proof.Wire_3_5.UnionMachine.FrontSemSUE
import Proof.Wire_3_5.UnionMachine.FrontSemTopS
import Proof.Wire_3_5.UnionMachine.PlanW2
import Proof.Wire_3_5.UnionMachine.PlanW3
import Proof.Wire_3_5.UnionMachine.FrontCostSUEBase


noncomputable section
set_option maxRecDepth 120000


/-! # The front's finish: the leaf-U residual `FrontsFWE3′` (paper v2, §H.5 and Lemma H.7)

**`frontsFWE3`** : `∀ l, Σ e, ∀ F, GateFreeOK l F → PlanW3.FrontsFWE3 e l F` — the residual of the union leaf, the `fronts`
argument of the union plan. At margin `e := costDeg l + 1` (the clock is the numeral `kclk`, `costDeg l + 1 ≤ kclk`), for
every coefficient, source work, primitive and language, C1's degree `dS`, the time factor `K_f = KfC + KfT`, and at
every `N₀` a front:
* at the recovered language (the live setup `recSetup2`: `𝒱_G = gateSV`, `q(N)` the ledger's): **`frontAtS`**, the
  machine `Front35.Top.topM` (the outer step's cold front end on the guessed pair: the dyadic length, the decoded pair
  within `q^G` gates, the `λ_a` guard, the source check, `H_Γ = Outer.Dat`, the PCPP of `H_Γ`; then the old chain), the
  reference output `FrontOutRef.outRef` at the capacities `capQ`, `RQ`, `RQ + 1`, the onset past `N₀` and the
  thresholds of `topFacts_ev`, `cost_ev` and `outRef_fields`, and the cost `2N + 6` below the onset,
  `K_f(q+1)^7(callBudget q + β(q))` past it;
* off it (the dead setup, `live = false`: no guess passes the outer step's guards): **`frontDead`**, the rejecting bank
  on every input.

Paper quantity of the main type: the front's output bank, decision, capacities and time at the PCPP output of `H_Γ`
(`FrontAtW3`, whose meaning `workerMeaning2` reads `S.request = requestAt … (Outer.Dat …)`). -/

set_option autoImplicit false
set_option maxRecDepth 120000

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

/-- The front's margin degree bound holds at `e = costDeg l + 1`: `costDeg + 1 = 41 ≤ kclk`. -/
theorem hdegS (l : Literals) : costDeg l + 1 ≤ kE l (costDeg l + 1) := by
  show 40 + 1 ≤ kclk
  rw [kclk_eq]

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
  1 + FrontPh1.PH1 (kE l e) + Front35.Ph2.PH2 (cnwS l F e coef A L hL) +
    (FrontRest.RS Mode.thr (DwS l F e coef A L hL) (IUE l F e coef A).descDeg (IUE l F e coef A).carrierDeg
      (DeS l F e coef A) (DtS l F e coef A L hL) c +
    FrontRest.RS Mode.sym (DwS l F e coef A L hL) (IUE l F e coef A).descDeg (IUE l F e coef A).carrierDeg
      (DeS l F e coef A) (DtS l F e coef A L hL) c)

theorem tf_one (c : Plan.C1At (dS l F e coef A L hL)) : 1 ≤ tfS l F e coef A L hL c := by unfold tfS; omega

theorem tf_p1 (c : Plan.C1At (dS l F e coef A L hL)) : 1 + FrontPh1.PH1 (kE l e) ≤ tfS l F e coef A L hL c := by
  unfold tfS; omega

theorem tf_p2 (c : Plan.C1At (dS l F e coef A L hL)) :
    1 + FrontPh1.PH1 (kE l e) + Front35.Ph2.PH2 (cnwS l F e coef A L hL) ≤ tfS l F e coef A L hL c := by
  unfold tfS; omega

theorem tf_r (c : Plan.C1At (dS l F e coef A L hL)) : ∀ m : Mode,
    1 + FrontPh1.PH1 (kE l e) + Front35.Ph2.PH2 (cnwS l F e coef A L hL) +
      FrontRest.RS m (DwS l F e coef A L hL) (IUE l F e coef A).descDeg (IUE l F e coef A).carrierDeg
        (DeS l F e coef A) (DtS l F e coef A L hL) c ≤ tfS l F e coef A L hL c := by
  intro m; cases m <;> unfold tfS <;> omega

/-- **The front's machine** at onset `C`. -/
noncomputable def topS (c : Plan.C1At (dS l F e coef A L hL)) (P : FusedPrimitive (IUE l F e coef A)) (C : ℕ) :=
  Front35.Top.topM P (tfS l F e coef A L hL c) (tf_one l F e coef A L hL c) (cnwS l F e coef A L hL) (kE l e)
    (gateApad l) (recOracleDeg l) (DwS l F e coef A L hL) (IUE l F e coef A).descDeg (IUE l F e coef A).carrierDeg
    (DeS l F e coef A) (DtS l F e coef A L hL) c (tf_p1 l F e coef A L hL c) (tf_p2 l F e coef A L hL c)
    (tf_r l F e coef A L hL c) C (KwS l F e coef A L hL) (KbS l F e coef A L hL) (DbS l F e coef A L hL) true
    (gateCParams1 l).ζ (gateCδ1 l) (CeS l F e coef A) (CtS l F e coef A L hL) F.cr
    (FrontPw.pwW (KbS l F e coef A L hL) (DbS l F e coef A L hL) true (gateCParams1 l).ζ (gateCδ1 l) (aVS l) (bVS l)
      (aTS l) (bTS l)) F.cr (32 * coef + 1) (gate0 l F).E.Amain

/-- **The front's onset** at the live setup: past `N₀`, `topFacts_ev`, `cost_ev` and `outRef_fields`. -/
noncomputable def onS (h : L = recL l (kE l e)) (hcoef : 1 ≤ coef) (P : FusedPrimitive (IUE l F e coef A))
    (hdeg : costDeg l + 1 ≤ kE l e) (c : Plan.C1At (dS l F e coef A L hL)) (N₀ : ℕ) : ℕ :=
  max N₀ (max (Classical.choose (topFacts_ev l F e coef A L hL h c))
    (max (Classical.choose (FrontCostSUE.cost_ev l F e coef A L hL h hcoef hdeg c))
      (Classical.choose (FrontCaps.outRef_fields l F e coef A L hL hcoef P (FrontCaps.gridFacts_SUE l F e coef A L hL)))))

/-- **The front's cost**: `2N + 6` below the onset, `K_f(q+1)^7(callBudget q + β(q))` past it. -/
noncomputable def costS (c : Plan.C1At (dS l F e coef A L hL)) (on Kf N : ℕ) : ℕ :=
  if N < on then 2 * N + 6 else
    Kf * ((BU l F e coef A).q N + 1) ^ (callDegMargin - 1) *
      ((BU l F e coef A).callBudget ((BU l F e coef A).q N) + c.budgetAt (BU l F e coef A) ((BU l F e coef A).q N))

/-- The front's reference output at the live setup. -/
noncomputable abbrev outS (h : L = recL l (kE l e)) (hcoef : 1 ≤ coef) (P : FusedPrimitive (IUE l F e coef A))
    (hdeg : costDeg l + 1 ≤ kE l e) (c : Plan.C1At (dS l F e coef A L hL)) (N₀ : ℕ) :=
  FrontOutRef.outRef (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
    (onS l F e coef A L hL h hcoef P hdeg c N₀) (fun N => FrontCaps.capQ l F e coef A ((BU l F e coef A).q N))
    (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N))
    (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1)

/-- **The front's run** at every input and witness: `top_run` enlarged to the cost. -/
theorem run_S (h : L = recL l (kE l e)) (hcoef : 1 ≤ coef) (P : FusedPrimitive (IUE l F e coef A))
    (hdeg : costDeg l + 1 ≤ kE l e) (c : Plan.C1At (dS l F e coef A L hL)) (N₀ N : ℕ) (x : BitInput N) (w : List Bool)
    (hw : w.length = N / 16) :
    ∃ (Hf : Fin (NW P (tfS l F e coef A L hL c)) → ℕ) (Af' : Fin (NW P (tfS l F e coef A L hL c)) → List Bool),
      Step (topS l F e coef A L hL c P (onS l F e coef A L hL h hcoef P hdeg c N₀))
        (costS l F e coef A L hL c (onS l F e coef A L hL h hcoef P hdeg c N₀) (FrontCaps.KfC l F + KfT l F) N)
        (fun _ => 0) (entryA x w) Hf Af' ∧
      (∀ i, Hf (lp P (tfS l F e coef A L hL c) i) =
        bankH P ((outS l F e coef A L hL h hcoef P hdeg c N₀ N x w).kept P) i) ∧
      (∀ i, Af' (lp P (tfS l F e coef A L hL c) i) = bankA P (outS l F e coef A L hL h hcoef P hdeg c N₀ N x w).cap
        (outS l F e coef A L hL h hcoef P hdeg c N₀ N x w).R (outS l F e coef A L hL h hcoef P hdeg c N₀ N x w).Lg
        ((outS l F e coef A L hL h hcoef P hdeg c N₀ N x w).kept P) i) := by
  have hon1 : Classical.choose (topFacts_ev l F e coef A L hL h c) ≤ onS l F e coef A L hL h hcoef P hdeg c N₀ := by
    unfold onS; omega
  have hon2 : Classical.choose (FrontCostSUE.cost_ev l F e coef A L hL h hcoef hdeg c) ≤
      onS l F e coef A L hL h hcoef P hdeg c N₀ := by
    unfold onS; omega
  have hv0 : (SUE l F e coef A L hL).params.v0 = (aVS l : ℚ) / bVS l := by
    rw [FrontSemSUE.sue_v0]; exact num_div_den _ (gateParams1 l).v0_pos.le
  have hτ : (SUE l F e coef A L hL).params.threshold = (aTS l : ℚ) / bTS l := by
    rw [FrontSemSUE.sue_thr]; exact num_div_den _ (thr_nonneg l)
  obtain ⟨Hf, Af', s, h1, h2⟩ := FrontSemRun.top_run P (tfS l F e coef A L hL c) (tf_one l F e coef A L hL c)
    (cnwS l F e coef A L hL) (kE l e) (gateApad l) (recOracleDeg l) (DwS l F e coef A L hL) (DeS l F e coef A)
    (DtS l F e coef A L hL) c (tf_p1 l F e coef A L hL c) (tf_p2 l F e coef A L hL c) (tf_r l F e coef A L hL c)
    (onS l F e coef A L hL h hcoef P hdeg c N₀) (KwS l F e coef A L hL) (gateZeta_pos l) (gateZeta_lt l)
    (KbS l F e coef A L hL) (DbS l F e coef A L hL) (gateCδ1 l) (CeS l F e coef A) (CtS l F e coef A L hL) F.cr
    (MSS l F e coef A L hL ((SUE l F e coef A L hL).width N)) (aVS l) (bVS l) (aTS l) (bTS l) F.cr
    (32 * coef + 1) (gate0 l F).E.Amain (FrontSemSUE.sue_parity l F e coef A L hL)
    (FrontSemSUE.sue_const l F e coef A L hL) (by show 2 ≤ 2; exact le_rfl) (by show 4 ≤ 26; omega)
    (FrontCaps.gridFacts_SUE l F e coef A L hL) (FrontSemSUE.sue_gridSize l F e coef A L hL)
    (FrontSemSUE.sue_gridMass l F e coef A L hL) (Rat.den_pos _) (Rat.den_pos _) hv0 hτ (fun _ => rfl)
    (fun N => FrontCaps.capQ l F e coef A ((BU l F e coef A).q N))
    (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N))
    (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1) x w hw
    (fun hCN => Classical.choose_spec (topFacts_ev l F e coef A L hL h c) N (le_trans hon1 hCN))
  refine ⟨Hf, Af', Step.enlarge s ?_, h1, h2⟩
  unfold costS
  split_ifs with hN
  · unfold FrontSemRun.costOf
    rw [if_pos hN]
  · have hc := Classical.choose_spec (FrontCostSUE.cost_ev l F e coef A L hL h hcoef hdeg c) N (by omega)
      (onS l F e coef A L hL h hcoef P hdeg c N₀) (by omega) x w hw
    refine hc.trans ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

/-- **The front at the live pinned setup** (residual U0–U5 with the atom test): `K_f = KfC + KfT`, `A_f = 8`. -/
noncomputable def frontAtS (h : L = recL l (kE l e)) (hcoef : 1 ≤ coef) (P : FusedPrimitive (IUE l F e coef A))
    (hdeg : costDeg l + 1 ≤ kE l e) (c : Plan.C1At (dS l F e coef A L hL)) (N₀ : ℕ) :
    PlanW3.FrontAtW3 P (SUE l F e coef A L hL) c 8 (FrontCaps.KfC l F + KfT l F) N₀ where
  tf := tfS l F e coef A L hL c
  sf := _
  M := topS l F e coef A L hL c P (onS l F e coef A L hL h hcoef P hdeg c N₀)
  cost := costS l F e coef A L hL c (onS l F e coef A L hL h hcoef P hdeg c N₀) (FrontCaps.KfC l F + KfT l F)
  onset := onS l F e coef A L hL h hcoef P hdeg c N₀
  honset := le_max_left _ _
  callOk := FrontOutRef.callOkI (I := IUE l F e coef A)
  hok := fun _ _ _ _ r _ => FrontOutRef.callOkI_iff r
  out := outS l F e coef A L hL h hcoef P hdeg c N₀
  run := fun N x w hw => run_S l F e coef A L hL h hcoef P hdeg c N₀ N x w hw
  loop := (Classical.choose_spec (FrontCaps.outRef_fields l F e coef A L hL hcoef P
    (FrontCaps.gridFacts_SUE l F e coef A L hL)) (onS l F e coef A L hL h hcoef P hdeg c N₀) (by unfold onS; omega)).1
  capPos := fun N x w _ => FrontOutRef.outRef_capPos (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
    _ _ _ _ (fun N => FrontCaps.capQ_pos l F e coef A _) N x w
  accFit := (Classical.choose_spec (FrontCaps.outRef_fields l F e coef A L hL hcoef P
    (FrontCaps.gridFacts_SUE l F e coef A L hL)) (onS l F e coef A L hL h hcoef P hdeg c N₀) (by unfold onS; omega)).2.1
  sem := fun N x w hw => FrontOutRef.outRef_sem P (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
    _ _ _ _ N x w hw
  rej := fun N x w _ hN => FrontOutRef.outRef_rej (SUE l F e coef A L hL) (FrontCaps.gridFacts_SUE l F e coef A L hL)
    _ _ _ _ N x w hN
  costRej := fun N _ hN => by
    show costS l F e coef A L hL c (onS l F e coef A L hL h hcoef P hdeg c N₀) (FrontCaps.KfC l F + KfT l F) N ≤
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
      (FrontCaps.gridFacts_SUE l F e coef A L hL)) (onS l F e coef A L hL h hcoef P hdeg c N₀)
        (by unfold onS; omega)).2.2.1 N x w hw hN hne).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  capAcc := fun N x w hw hN =>
    ((Classical.choose_spec (FrontCaps.outRef_fields l F e coef A L hL hcoef P
      (FrontCaps.gridFacts_SUE l F e coef A L hL)) (onS l F e coef A L hL h hcoef P hdeg c N₀)
        (by unfold onS; omega)).2.2.2 N x w hw hN).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))

/-- Past a threshold the per-call budget is positive. -/
theorem callBudget_pos_ev (hcoef : 1 ≤ coef) : ∃ N₂ : ℕ, ∀ N, N₂ ≤ N →
    1 ≤ (BU l F e coef A).callBudget ((BU l F e coef A).q N) := by
  have hq : Filter.Tendsto (BU l F e coef A).q Filter.atTop Filter.atTop :=
    Ledger.tendsto_nativeWidth (kE l e) (gate0 l F).Apad
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (hq.eventually_ge_atTop 1)
  refine ⟨N₂, fun N hN => ?_⟩
  have hlow := FrontCaps.callBudget_lower l F e coef A ((BU l F e coef A).q N)
  have h1 := hN₂ N hN
  have : 1 ≤ coef * (2 ^ ((BU l F e coef A).q N - (BU l F e coef A).kOf ((BU l F e coef A).q N) / 4) *
      (BU l F e coef A).q N ^ (gate0 l F).E.Amain) :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by positivity) (by positivity)))
  omega

/-- **The dead front** (off the recovered language, `live = false`): the rejecting bank on every input; no guess
passes the outer step's guards, so the worker's meaning is false. -/
noncomputable def frontDead (h : L ≠ recL l (kE l e)) (hcoef : 1 ≤ coef) (P : FusedPrimitive (IUE l F e coef A))
    {d : ℕ} (c : Plan.C1At d) (N₀ : ℕ) :
    PlanW3.FrontAtW3 P (SUE l F e coef A L hL) c 8 (FrontCaps.KfC l F + KfT l F) N₀ where
  tf := 1
  sf := _
  M := FrontGate.rejM P 1
  cost := fun _ => 3
  onset := max N₀ (Classical.choose (callBudget_pos_ev l F e coef A hcoef))
  honset := le_max_left _ _
  callOk := FrontOutRef.callOkI (I := IUE l F e coef A)
  hok := fun _ _ _ _ r _ => FrontOutRef.callOkI_iff r
  out := fun _ _ _ => FrontGate.rejOut
  run := fun N x w _ => by
    obtain ⟨H', A', s, hH, hA, -⟩ := FrontGate.rej_step P 1 (fun _ => 0) (entryA x w) (fun _ => rfl)
      (fun i => FrontGate.entryA_lp P 1 x w i)
    refine ⟨H', A', s, fun i => by rw [FrontGate.rejOut_kept]; exact hH i, fun i => ?_⟩
    rw [FrontGate.rejOut_kept]; exact hA i
  loop := fun _ _ _ _ hne => absurd rfl hne
  capPos := fun _ _ _ _ => le_rfl
  accFit := fun _ _ _ _ i => by
    rw [FrontGate.rejOut_keptEnd]
    show FrontGate.rejKept.acc i ≤ 1
    fin_cases i <;> simp [FrontGate.rejKept, FrontGate.rejAcc]
  sem := fun N x w _ => by
    rw [FrontGate.rejOut_keptEnd]
    simp only [FrontGate.rejKept]
    rw [FrontGate.decision_rej]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨-, -, hrun⟩
    unfold unionSlackRun at hrun
    split at hrun
    · exact Bool.noConfusion hrun
    · rename_i g _
      unfold unionSlackCheck at hrun
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrun
      have := hrun.1.1.1
      rw [FrontSemSUE.sue_dead l F e coef A L hL h] at this
      exact Bool.noConfusion this
  rej := fun _ _ _ _ _ => ⟨rfl, rfl⟩
  costRej := fun N _ _ => by
    show 3 ≤ 8 * (N + 1) ^ aE l e
    have h1 : 1 ≤ (N + 1) ^ aE l e := Nat.one_le_pow _ _ (by omega)
    omega
  costAcc := fun N _ _ => by
    have h1 : 1 ≤ (N + 1) ^ aE l e := Nat.one_le_pow _ _ (by omega)
    have : 3 ≤ 8 * (N + 1) ^ aE l e := by omega
    exact le_trans this (Nat.le_add_right _ _)
  len := fun _ _ _ _ _ hne => absurd rfl hne
  perCall := fun _ _ _ _ _ hne => absurd rfl hne
  capAcc := fun N _ _ _ hN => by
    have hcb := Classical.choose_spec (callBudget_pos_ev l F e coef A hcoef) N (le_trans (le_max_right _ _) hN)
    have h1 : 1 ≤ ((BU l F e coef A).q N + 1) ^ (callDegMargin - 1) := Nat.one_le_pow _ _ (by omega)
    have h2 : 2 ≤ FrontCaps.KfC l F + KfT l F := by
      unfold FrontCaps.KfC KfT
      have := Nat.one_le_two_pow (n := (gate0 l F).E.Amain)
      omega
    show 1 + 1 ≤ _
    calc 1 + 1 ≤ 2 * 1 * 1 := by norm_num
      _ ≤ (FrontCaps.KfC l F + KfT l F) * ((BU l F e coef A).q N + 1) ^ (callDegMargin - 1) *
          (BU l F e coef A).callBudget ((BU l F e coef A).q N) :=
        Nat.mul_le_mul (Nat.mul_le_mul h2 h1) hcb

end SUE

/-- **The fronts at one literal set and gate**, at margin `costDeg l + 1`: the live front at the recovered language,
the dead front elsewhere. -/
noncomputable def frontsS (l : Literals) (F : GateFree l) : PlanW3.FrontsFWE3 (costDeg l + 1) l F := by
  classical
  exact ⟨8, fun coef hcoef A P L hL => ⟨dS l F (costDeg l + 1) coef A L hL, fun c =>
    ⟨FrontCaps.KfC l F + KfT l F, fun N₀ =>
      if h : L = recL l (kE l (costDeg l + 1)) then
        frontAtS l F (costDeg l + 1) coef A L hL h hcoef P (hdegS l) c N₀
      else frontDead l F (costDeg l + 1) coef A L hL h hcoef P c N₀⟩⟩⟩

/-- **The fronts finish** (residual U0–U5 with the atom test, the union leaf's residual): `PlanW3.union_planW3`'s `fronts`. -/
noncomputable def frontsFWE3 : ∀ l : Literals, Σ e : ℕ, ∀ F : GateFree l, GateFreeOK l F → PlanW3.FrontsFWE3 e l F :=
  fun l => ⟨costDeg l + 1, fun F _ => frontsS l F⟩

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFinish

end
