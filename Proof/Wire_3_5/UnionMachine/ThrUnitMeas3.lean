import Lean
import Proof.Wire_3_5.UnionMachine.ThrUnitMeas2
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.RadAbsorb
import Proof.Wire_3_5.UnionMachine.RadSetupB5
import Proof.Wire_3_5.UnionMachine.ThrDecIface
import Proof.Wire_3_5.UnionMachine.ThrUnitIface
import Proof.Wire_3_5.UnionMachine.ThrUnitIface5
import Proof.Wire_3_5.UnionMachine.ThrUnitMeas
import Proof.Wire_3_5.UnionMachine.ThrUnitRun
import Proof.Wire_3_5.UnionMachine.ThrUnitMeas3Base


noncomputable section
set_option maxRecDepth 4096


/-! # The THR unit's measure absorbed by `Ψ_T`, part 3: the call's measure `measC ≤ c·2^{K_q·Ψ_T}`

At a THR call of a gate with `C_D ≥ 1` (`L = ⌈log₂(n+2)⌉`, `Ψ_T = loadThr C_D k L B_T`, P3:3094-3100):
`L⁴ ≤ Ψ_T` (`psi_L4`); the RADIX measures `2^{(3lb+1)(26L+7) + K_R L² + 8} ≤ 2^{K_1·Ψ_T}` through `lb·L ≤ c_Ab·Ψ_T`
(`ThrUnit.lb_absorbT`, `expo_rad`); the FILTER setup's arguments `2^{K_F L²}` and its pipeline's bound
`K_f·(f+2)^{D_f(f_e L+2)} ≤ K_f·2^{D_f(f_e+2)(K_F+1)Ψ_T}` (`expo_filt`); the decode front's need and bound
(quasi-polynomial, `2^{K·L²}`); the data counts. Hence **`measC_le`**: `measC ≤ c·2^{K_q·Ψ_T}` with the coefficient
`c = C_n + C_b + 16K_t + 32 + K_f + 3` (after the gate) and the exponent `K_q` from `l`, `f_e`, the decode front's
exponent bound `D₀`, `D_f` and `D_t` (before the gate).

Paper quantity: the THR unit's per-call measure within the preprocessing class `2^{O(Ψ_T)}` (P3:3089-3108). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (pow_N_le one_le_L n2_le_L pow_mono_mul)

/-- **The measure's exponent** (from `l`, `f_e`, the decode front's `D₀`, `D_f`, `D_t`). -/
noncomputable def Kq (l : Literals) (fe D0 Df Dt : ℕ) : ℕ :=
  4 * D0 + (99 * RadAbsorb.cAb l + KR l + 41) + KF l fe + Df * (fe + 2) * (KF l fe + 2) + (Dt + 26) + 1

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (a' : ℕ) (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
  (hs : (callInputs l F kclk coef A a ha).StarAt n)
include hcall hs

/-- **The call's measure below `c·2^{K_q·Ψ_T}`.** -/
theorem measC_le {x : ℕ} (D : ThrDec.ThrDecFront x l F) (D0 : ℕ) (hD0 : ThrUnit.decDeg D ≤ D0) (hCD : 1 ≤ F.CD)
    (Kf Df Kt Dt : ℕ)
    (hKt : ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap,
      v ≤ Kt * (n + 1) ^ Dt) :
    ThrUnitRun.measC D Kf Df kclk coef A a ha n hs a' ha' Cs carriers translation ≤
      (D.Cn + D.Cb + (16 * Kt + 32) + Kf + 3) * 2 ^ (Kq l F.filterErrDeg D0 Df Dt * (loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n))) := by
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := hLd ▸ one_le_L n
  obtain ⟨Ψ, hΨ⟩ : ∃ p, p = (loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n)) := ⟨_, rfl⟩
  have h4 : L * L * (L * L) ≤ Ψ := by rw [hΨ, ← hLd]; exact psi_L4 _ _ _ _ hCD
  have hLL : 1 ≤ L * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hLY : L ≤ L * L := Nat.le_mul_of_pos_left L hL1
  have hY : L * L ≤ Ψ := le_trans (Nat.le_mul_of_pos_right _ hLL) h4
  have hLΨ : L ≤ Ψ := hLY.trans hY
  rw [← hΨ]
  obtain ⟨K, hK⟩ : ∃ k, k = Kq l F.filterErrDeg D0 Df Dt := ⟨_, rfl⟩
  rw [← hK]
  have hKpos : 1 ≤ K := by rw [hK]; unfold Kq; omega
  have hEK : ∀ c, c ≤ K → c * Ψ ≤ K * Ψ := fun c hc => Nat.mul_le_mul_right _ hc
  -- the decode front
  have hDn : D.Dn ≤ D0 ∧ D.Kn ≤ D0 ∧ D.Db ≤ D0 ∧ D.Kb ≤ D0 := by
    unfold ThrUnit.decDeg at hD0
    exact ⟨le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hD0,
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hD0,
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hD0,
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hD0⟩
  have hq : ∀ (v C Dd Kd : ℕ), Dd ≤ D0 → Kd ≤ D0 → PrimThrW.RadSetup.QuasiBounded v n C Dd Kd → v ≤ C * 2 ^ (K * Ψ) := by
    intro v C Dd Kd h1 h2 hv
    unfold PrimThrW.RadSetup.QuasiBounded at hv
    have p1 : (n + 2) ^ Dd ≤ 2 ^ (Dd * L) := by have := pow_N_le n Dd; rw [← hLd] at this; exact this
    have p2 : Kd * Nat.clog 2 (n + 2) ^ 2 = Kd * (L * L) := by rw [← hLd, sq]
    rw [p2] at hv
    have p3 : Dd * L + Kd * (L * L) ≤ K * Ψ := by
      have q1 : Dd * L ≤ D0 * Ψ := Nat.mul_le_mul h1 hLΨ
      have q2 : Kd * (L * L) ≤ D0 * Ψ := Nat.mul_le_mul h2 hY
      have q3 : 4 * D0 * Ψ ≤ K * Ψ := hEK _ (by rw [hK]; unfold Kq; omega)
      have e : 4 * D0 * Ψ = 4 * (D0 * Ψ) := by ring
      omega
    calc v ≤ C * (n + 2) ^ Dd * 2 ^ (Kd * (L * L)) := hv
      _ ≤ C * 2 ^ (Dd * L) * 2 ^ (Kd * (L * L)) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ p1)
      _ = C * 2 ^ (Dd * L + Kd * (L * L)) := by rw [pow_add]; ring
      _ ≤ C * 2 ^ (K * Ψ) := Nat.mul_le_mul_left _ (two_pow_le_of p3)
  have d1 := hq _ _ _ _ hDn.1 hDn.2.1 (D.need_q n)
  have d2 := hq _ _ _ _ hDn.2.2.1 hDn.2.2.2 (D.bound_q n)
  -- the counts
  have d3 : (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers).length ≤ (16 * Kt + 32) * 2 ^ (K * Ψ) := by
    have := u_le l F kclk coef A a ha ha' Cs carriers translation hcall hs Kt Dt hKt
    rw [← hLd] at this
    exact this.trans (Nat.mul_le_mul_left _ (two_pow_le_of ((Nat.mul_le_mul_left _ hLΨ).trans
      (hEK _ (by rw [hK]; unfold Kq; omega)))))
  -- the RADIX measures
  have hlb := ThrUnit.lb_absorbT l F hCD kclk coef A a ha ha' Cs carriers translation hcall hs
  rw [← hΨ, ← hLd] at hlb
  have d4 : ThrUnitRun.rSup kclk coef A a ha n hs a' ha' Cs carriers translation ≤ 2 ^ (K * Ψ) := by
    unfold ThrUnitRun.rSup
    apply Finset.sup_le
    intro p hp
    obtain ⟨-, hrow⟩ := Finset.mem_product.mp hp
    have h := radMeas5_le l F kclk coef A a ha ha' Cs carriers translation hcall hs p.1 p.2 (Finset.mem_range.mp hrow)
    rw [← hLd] at h
    refine h.trans (two_pow_le_of ?_)
    exact (expo_rad _ L Ψ (RadAbsorb.cAb l) (KR l) hL1 h4 hlb).trans (hEK _ (by rw [hK]; unfold Kq; omega))
  -- the FILTER setup's arguments
  have d5' : ThrUnitRun.fSup kclk coef A a ha n hs a' Cs carriers ≤ 2 ^ (KF l F.filterErrDeg * (L * L)) := by
    unfold ThrUnitRun.fSup
    apply Finset.sup_le
    intro p hp
    obtain ⟨hjr, hrow⟩ := Finset.mem_product.mp hp
    have h := fArgs_le l F kclk coef A a ha ha' Cs carriers translation hcall hs p.1 p.2 (Finset.mem_range.mp hjr)
      (Finset.mem_range.mp hrow)
    rw [← hLd] at h
    exact h
  have d5 : ThrUnitRun.fSup kclk coef A a ha n hs a' Cs carriers ≤ 2 ^ (K * Ψ) :=
    d5'.trans (two_pow_le_of ((Nat.mul_le_mul_left _ hY).trans (hEK _ (by rw [hK]; unfold Kq; omega))))
  -- the FILTER pipeline's bound
  have herr : ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp = F.filterErrDeg * L := by rw [hLd]; rfl
  have d6 : Kf * (ThrUnitRun.fSup kclk coef A a ha n hs a' Cs carriers + 2) ^ (Df * (((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + 2)) ≤
      Kf * 2 ^ (K * Ψ) := by
    apply Nat.mul_le_mul_left
    have f1 : ThrUnitRun.fSup kclk coef A a ha n hs a' Cs carriers + 2 ≤ 2 ^ (KF l F.filterErrDeg * (L * L) + 2) := by
      have e : 2 ^ (KF l F.filterErrDeg * (L * L) + 2) = 4 * 2 ^ (KF l F.filterErrDeg * (L * L)) := by ring
      have : 1 ≤ 2 ^ (KF l F.filterErrDeg * (L * L)) := Nat.one_le_two_pow
      omega
    have f2 := pow_mono_mul (Df * (((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + 2)) f1
    refine f2.trans (two_pow_le_of ?_)
    rw [herr]
    have f3 := expo_filt F.filterErrDeg L Ψ (KF l F.filterErrDeg) Df hL1 h4
    exact f3.trans (hEK _ (by rw [hK]; unfold Kq; omega))
  have hP : 1 ≤ 2 ^ (K * Ψ) := Nat.one_le_two_pow
  unfold ThrUnitRun.measC
  have e : (D.Cn + D.Cb + (16 * Kt + 32) + Kf + 3) * 2 ^ (K * Ψ) =
      D.Cn * 2 ^ (K * Ψ) + D.Cb * 2 ^ (K * Ψ) + (16 * Kt + 32) * 2 ^ (K * Ψ) + Kf * 2 ^ (K * Ψ) + 3 * 2 ^ (K * Ψ) := by ring
  omega

end Call

end NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas

end
