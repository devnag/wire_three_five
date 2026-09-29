import Proof.Wire_3_5.Primitive.SeedFix.ThrTB2
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ7
import Proof.Wire_3_5.UnionMachine.ThrDimG

/-! # THRTAIL T-B, part 3: the THR dimension at a call

T-A's stage `thrDimStageG l F K_L K_f` at the call's star parameters `P`: its dimension `m_T P` lies
between `k + L + K_L·L² + K_f·Ψ_T` and `k + L + K_L·L² + 8K_f·Ψ_T` (`m_ge`, `m_le`; `mOf P = 2k_h + L = k + L`,
`ψ_T(P) = Ψ_T` at the call's budget, P3:3094-3107). At `K_L = kLT l f_e D₀`, `K_f = D₀ + 1` the dimension covers the
unit's measure (`meas ≤ D₀·2^m`, THRU4's `meas_le`), the unit count (`thrTOT ≤ C_L·2^m`, `tot_eq` + the decode's
atom bounds) and the request (`|w| ≤ 2^m`, `ThrMeas.word_le`).

* `kLT`, `kFT`, `cLT`; **`dim_ge`**, **`dim_le`**, **`meas_le_dim`**, **`tot_le_dim`**, **`w_le_dim`**.

Paper quantity of the main type: the THR writer's dimension `2^{m_T}`, `m_T = Θ(Ψ_T)` (P3:3094-3107). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.UnionMachine

/-- The dimension's `L²` coefficient (from `(l, f_e, D₀)`). -/
noncomputable def kLT (l : Literals) (fe D0 : ℕ) : ℕ :=
  D0 + ThrDecF.aE l fe + 2 * ThrDecF.dT l + ThrMeas.KR l + 8

/-- The dimension's load multiplier (from `D₀`). -/
def kFT (D0 : ℕ) : ℕ := D0 + 1

/-- The loop's coefficient (from `F`): `11·Q_F² + 1`. -/
noncomputable def cLT (l : Literals) (F : GateFree l) : ℕ := 11 * (ThrDecF.qF l F * ThrDecF.qF l F) + 1

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n)

theorem psiT_eq : ThrDim.psiT l F.CD ((callInputs l F kclk coef A a ha).starParams n hs) =
    loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
      (((gate0 l F).budget kclk coef A a ha).capOf .thr n) := rfl

theorem mOf_eq : NumsX.mOf ((callInputs l F kclk coef A a ha).starParams n hs) =
    ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) := by
  have h := FinalPass.SymFr.kh_two l F kclk coef A a ha hs
  unfold SeedFix.callKh at h
  unfold NumsX.mOf
  rw [h]
  rfl

/-- **The dimension's lower bound** at the call. -/
theorem dim_ge (KL Kf : ℕ) :
    ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) + KL * Nat.clog 2 (n + 2) ^ 2 +
        Kf * loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
          (((gate0 l F).budget kclk coef A a ha).capOf .thr n) ≤
      (UnionMachine.ThrDimB.thrDimStageG l F KL Kf).mT ((callInputs l F kclk coef A a ha).starParams n hs) := by
  have h := (UnionMachine.ThrDimB.thrDimStageG l F KL Kf).m_ge ((callInputs l F kclk coef A a ha).starParams n hs)
  unfold PrimThrW.Shell2.mOfT at h
  rw [mOf_eq l F kclk coef A a ha hs, psiT_eq l F kclk coef A a ha hs] at h
  exact h

/-- **The dimension's upper bound** at the call. -/
theorem dim_le (KL Kf : ℕ) :
    (UnionMachine.ThrDimB.thrDimStageG l F KL Kf).mT ((callInputs l F kclk coef A a ha).starParams n hs) ≤
      ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) + KL * Nat.clog 2 (n + 2) ^ 2 +
        8 * Kf * loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
          (((gate0 l F).budget kclk coef A a ha).capOf .thr n) := by
  have h := (UnionMachine.ThrDimB.thrDimStageG l F KL Kf).m_le ((callInputs l F kclk coef A a ha).starParams n hs)
  unfold PrimThrW.Shell2.mOfT at h
  rw [mOf_eq l F kclk coef A a ha hs, psiT_eq l F kclk coef A a ha hs] at h
  exact h

end Call

section Cover
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
  (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
  (hs : (callInputs l F kclk coef A a ha).StarAt n)
include hcall hs

/-- **The dimension covers the unit's measure**: `meas ≤ D₀·2^m`. -/
theorem meas_le_dim (U : ThrUnit.ThrUnitSpec4 l F) (fe D0 : ℕ) (hKm : U.Km ≤ D0) (hDm : U.Dm ≤ D0) :
    U.meas kclk coef A a ha n hs a' ha' Cs carriers translation ≤
      D0 * 2 ^ (UnionMachine.ThrDimB.thrDimStageG l F (kLT l fe D0) (kFT D0)).mT
        ((callInputs l F kclk coef A a ha).starParams n hs) := by
  have h := U.meas_le kclk coef A a ha n hs a' ha' Cs carriers translation hcall
  have hm := dim_ge l F kclk coef A a ha hs (kLT l fe D0) (kFT D0)
  obtain ⟨m, hmd⟩ : ∃ x, x = (UnionMachine.ThrDimB.thrDimStageG l F (kLT l fe D0) (kFT D0)).mT
      ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  rw [← hmd] at hm ⊢
  obtain ⟨T, hT⟩ : ∃ x, x = loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
      (((gate0 l F).budget kclk coef A a ha).capOf .thr n) := ⟨_, rfl⟩
  rw [← hT] at h hm
  obtain ⟨L, hLd⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd] at hm
  have hL1 : 1 ≤ L := hLd ▸ FinalPass.SymFr.one_le_L n
  have hn2 : n + 2 ≤ 2 ^ L := hLd ▸ FinalPass.SymFr.n2_le_L n
  have p1 : (n + 2) ^ U.Dm ≤ 2 ^ (D0 * L ^ 2) := by
    calc (n + 2) ^ U.Dm ≤ (2 ^ L) ^ U.Dm := Nat.pow_le_pow_left hn2 _
      _ = 2 ^ (U.Dm * L) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ (D0 * L ^ 2) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hDm (by nlinarith))
  have p2 : 2 ^ (U.Km * T) ≤ 2 ^ (kFT D0 * T) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by unfold kFT; omega))
  have p3 : 2 ^ (D0 * L ^ 2) * 2 ^ (kFT D0 * T) ≤ 2 ^ m := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    have : D0 * L ^ 2 ≤ kLT l fe D0 * L ^ 2 := Nat.mul_le_mul_right _ (by unfold kLT; omega)
    omega
  calc U.meas kclk coef A a ha n hs a' ha' Cs carriers translation ≤ U.Km * (n + 2) ^ U.Dm * 2 ^ (U.Km * T) := h
    _ ≤ D0 * 2 ^ (D0 * L ^ 2) * 2 ^ (kFT D0 * T) := Nat.mul_le_mul (Nat.mul_le_mul hKm p1) p2
    _ = D0 * (2 ^ (D0 * L ^ 2) * 2 ^ (kFT D0 * T)) := by ring
    _ ≤ D0 * 2 ^ m := Nat.mul_le_mul_left _ p3

/-- **The dimension covers the call's units**: `thrTOT ≤ C_L·2^m`. -/
theorem tot_le_dim (fe D0 : ℕ) (hfe : F.filterErrDeg = fe) :
    ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers ≤
      cLT l F * 2 ^ (UnionMachine.ThrDimB.thrDimStageG l F (kLT l fe D0) (kFT D0)).mT
        ((callInputs l F kclk coef A a ha).starParams n hs) := by
  subst hfe
  have hm := dim_ge l F kclk coef A a ha hs (kLT l F.filterErrDeg D0) (kFT D0)
  obtain ⟨m, hmd⟩ : ∃ x, x = (UnionMachine.ThrDimB.thrDimStageG l F (kLT l F.filterErrDeg D0) (kFT D0)).mT
      ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  rw [← hmd] at hm ⊢
  rw [ThrDecF.tot_eq]
  have hsb := ThrDecF.sbT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have h2 := ThrDecF.hs_le l F kclk coef A a ha ha' Cs carriers translation hcall hs 2
  have h6 := ThrDecF.hs_le l F kclk coef A a ha ha' Cs carriers translation hcall hs 6
  have hkh := FinalPass.SymFr.kh_two l F kclk coef A a ha hs
  unfold SeedFix.callKh at hkh
  rw [hkh]
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  unfold ThrDecF.QY at h2 h6
  rw [pow_one] at h2 h6
  obtain ⟨L, hLd⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd] at hm h2 h6 hsb
  obtain ⟨k, hkd⟩ : ∃ x, x = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  rw [← hkd] at hm ⊢
  obtain ⟨sb, hsbd⟩ : ∃ x, x = ((callInputs l F kclk coef A a ha).filterParams .thr n).seedBits := ⟨_, rfl⟩
  rw [← hsbd] at hsb ⊢
  obtain ⟨Q, hQ⟩ : ∃ x, x = ThrDecF.qF l F := ⟨_, rfl⟩
  rw [← hQ] at h2 h6
  have hcl : cLT l F = 11 * (Q * Q) + 1 := by rw [hQ]; rfl
  rw [hcl]
  -- the exponents
  have hexp : sb + ThrDecF.dT l * (L * L) + ThrDecF.dT l * (L * L) + k ≤ m := by
    have a1 : ThrDecF.aE l F.filterErrDeg * (L * L) + 2 * ThrDecF.dT l * (L * L) ≤ kLT l F.filterErrDeg D0 * L ^ 2 := by
      rw [pow_two, ← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by unfold kLT; omega)
    have e2 : 2 * ThrDecF.dT l * (L * L) = ThrDecF.dT l * (L * L) + ThrDecF.dT l * (L * L) := by ring
    omega
  have p1 : 2 ^ sb * (Q * 2 ^ (ThrDecF.dT l * (L * L))) * (Q * 2 ^ (ThrDecF.dT l * (L * L))) * 2 ^ k =
      Q * Q * 2 ^ (sb + ThrDecF.dT l * (L * L) + ThrDecF.dT l * (L * L) + k) := by
    rw [pow_add, pow_add, pow_add]; ring
  have p2 : 2 ^ (sb + ThrDecF.dT l * (L * L) + ThrDecF.dT l * (L * L) + k) ≤ 2 ^ m :=
    Nat.pow_le_pow_right (by norm_num) hexp
  obtain ⟨H2, hH2⟩ : ∃ x, x = (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD
      2 0 := ⟨_, rfl⟩
  obtain ⟨H6, hH6⟩ : ∃ x, x = (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD
      6 0 := ⟨_, rfl⟩
  rw [← hH2] at h2 ⊢
  rw [← hH6] at h6 ⊢
  have q1 : 2 ^ sb * H2 * H6 * 2 ^ k ≤ Q * Q * 2 ^ m := by
    calc 2 ^ sb * H2 * H6 * 2 ^ k ≤ 2 ^ sb * (Q * 2 ^ (ThrDecF.dT l * (L * L))) * (Q * 2 ^ (ThrDecF.dT l * (L * L))) *
          2 ^ k := Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h6)
      _ = Q * Q * 2 ^ (sb + ThrDecF.dT l * (L * L) + ThrDecF.dT l * (L * L) + k) := p1
      _ ≤ Q * Q * 2 ^ m := Nat.mul_le_mul_left _ p2
  have q2 : 2 ^ sb * H2 * H6 * 2 ^ k * ((carriers.length + 1) * 3 + 2) ≤ Q * Q * 2 ^ m * 11 :=
    Nat.mul_le_mul q1 (by omega)
  have e3 : (11 * (Q * Q) + 1) * 2 ^ m = Q * Q * 2 ^ m * 11 + 2 ^ m := by ring
  have := Nat.one_le_two_pow (n := m)
  omega

/-- **The dimension covers the request**: `|w| ≤ 2^m`. -/
theorem w_le_dim (fe D0 : ℕ) :
    (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation).length ≤
      2 ^ (UnionMachine.ThrDimB.thrDimStageG l F (kLT l fe D0) (kFT D0)).mT
        ((callInputs l F kclk coef A a ha).starParams n hs) := by
  have h := ThrMeas.word_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hm := dim_ge l F kclk coef A a ha hs (kLT l fe D0) (kFT D0)
  refine le_trans h (Nat.pow_le_pow_right (by norm_num) ?_)
  have hL1 := FinalPass.SymFr.one_le_L n
  have a1 : (ThrMeas.KR l + 3) * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) ≤ kLT l fe D0 * Nat.clog 2 (n + 2) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul_right _ (by unfold kLT; omega)
  have a2 : 1 ≤ Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2) := by nlinarith
  have e : (ThrMeas.KR l + 3) * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) =
      ThrMeas.KR l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) + 3 * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) := by ring
  show ThrMeas.KR l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) + 3 ≤ _
  omega

end Cover

end NearCubicWires.WireExponent3_5.PrimT.ThrTB
