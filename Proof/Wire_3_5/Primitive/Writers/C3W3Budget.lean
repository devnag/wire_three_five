import Proof.Wire_3_5.Primitive.Writers.C3WBudgetA

/-! # The C3 writers' budget at the polynomial load premise

`C3Cost.call_budget` with the premise `h + Q' + m + pr ≤ c_N·(Ψ+1)·(n+1)^{D_N}`. The size's polynomial part is
raised to `(n+1)^{D₀+D_N}` (`omega_factsD`, `size_leD`, the size bound at any degree `D`), so the class is
`EW3 l D_N = 2^{(D₀+D_N+2)·d_G·Ψ}` (**`call_budget3`**); `k + L ≤ Ψ` (the load floor `C_D ≥ 1`) absorbs `(n+1)^{D_N}`.

Paper quantity of the main type: the writers' steps within the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108,
3170-3173). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.LocalBitMultitape NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.C3Mach NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.CompilerMachine.Pool

variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The writers' envelope at the polynomial premise.** -/
noncomputable def EW3 (l : Literals) (DN : ℕ) : Envelope :=
  EWc ((D0 + DN + 2) * dGm (Classical.choice l.eightSources.decomposition) DvC)

/-- **The size bound at degree `D`**: `(S₀+1)^d ≤ (K+1)^d·2^{(D+2)·d·Ψ}` once `S₀ ≤ K·2^k(n+1)^{D}(Ψ+1)` and
`k + L ≤ Ψ`. -/
theorem size_leD (n k psi L K S0 d D : ℕ) (hk : k + L ≤ psi) (hL : n + 2 ≤ 2 ^ L)
    (hS : S0 ≤ K * (2 ^ k * (n + 1) ^ D * (psi + 1))) :
    (S0 + 1) ^ d ≤ (K + 1) ^ d * 2 ^ ((D + 2) * d * psi) := by
  have h1 : 2 ^ k ≤ 2 ^ psi := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : n + 1 ≤ 2 ^ psi := le_trans (by omega) (le_trans hL (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h3 : (n + 1) ^ D ≤ (2 ^ psi) ^ D := Nat.pow_le_pow_left h2 _
  have h4 : psi + 1 ≤ 2 ^ psi := Nat.lt_two_pow_self
  have hΩ : 2 ^ k * (n + 1) ^ D * (psi + 1) ≤ 2 ^ ((D + 2) * psi) := by
    calc 2 ^ k * (n + 1) ^ D * (psi + 1) ≤ 2 ^ psi * (2 ^ psi) ^ D * 2 ^ psi := by gcongr
      _ = 2 ^ ((D + 2) * psi) := by rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
  have h5 : S0 + 1 ≤ (K + 1) * 2 ^ ((D + 2) * psi) := by
    calc S0 + 1 ≤ K * (2 ^ k * (n + 1) ^ D * (psi + 1)) + 2 ^ k * (n + 1) ^ D * (psi + 1) := by
          have : 0 < 2 ^ k * (n + 1) ^ D * (psi + 1) := by positivity
          omega
      _ = (K + 1) * (2 ^ k * (n + 1) ^ D * (psi + 1)) := by ring
      _ ≤ (K + 1) * 2 ^ ((D + 2) * psi) := Nat.mul_le_mul_left _ hΩ
  calc (S0 + 1) ^ d ≤ ((K + 1) * 2 ^ ((D + 2) * psi)) ^ d := Nat.pow_le_pow_left h5 _
    _ = (K + 1) ^ d * 2 ^ ((D + 2) * d * psi) := by rw [mul_pow, ← pow_mul]; ring_nf

theorem omega_factsD (n k psi DN : ℕ) :
    1 ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) ∧ n ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) ∧
      psi + 1 ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) ∧
      (∀ e, e ≤ D0 → (n + 1) ^ e ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1)) ∧
      (∀ e, e ≤ D0 → 2 ^ k * (n + 1) ^ e ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1)) ∧
      (psi + 1) * (n + 1) ^ DN ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hD : 1 ≤ D0 := by unfold D0; omega
  have hn : n + 1 ≤ (n + 1) ^ (D0 + DN) := Nat.le_self_pow (by omega) _
  have hp : 1 ≤ (n + 1) ^ (D0 + DN) := Nat.one_le_pow _ _ (by omega)
  have b1 : (n + 1) ^ (D0 + DN) ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by
    calc (n + 1) ^ (D0 + DN) = 1 * (n + 1) ^ (D0 + DN) * 1 := by ring
      _ ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by gcongr <;> omega
  have b2 : psi + 1 ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by
    calc psi + 1 = 1 * 1 * (psi + 1) := by ring
      _ ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by gcongr
  refine ⟨by omega, by omega, b2, fun e he => le_trans (Nat.pow_le_pow_right (by omega) (by omega)) b1,
    fun e he => ?_, ?_⟩
  · calc 2 ^ k * (n + 1) ^ e ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * 1 := by
          rw [mul_one]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := Nat.mul_le_mul_left _ (by omega)
  · calc (psi + 1) * (n + 1) ^ DN ≤ (psi + 1) * (n + 1) ^ (D0 + DN) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ = 1 * (n + 1) ^ (D0 + DN) * (psi + 1) := by ring
      _ ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by gcongr

/-- **The writer's steps at a call, in the class.** -/
theorem call_budget3 (DN : ℕ) (Gs : WriterIface.WriterStage)
    (sA : PrimT.GeoIface2.SideWriterAt l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha)
    (wA : PrimT.GeoIface2.WidthWriterAt l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha)
    (cA : PrimT.GeoIface2.ColsWriterAt l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha) (req : PrimRequest)
    (hcall : (callInputs l F kclk coef A a ha).Call req) (hs : (callInputs l F kclk coef A a ha).StarAt req.n)
    (gates : List (NormalizedThresholdGate ((callInputs l F kclk coef A a ha).starParams req.n hs).n)) (BG : ℕ)
    (hG : WriterIfaceJ.WriterRun Gs.M BG Gs.inS Gs.outS req.word (PrimT.C4Geo.gateField gates))
    (Ag cGx : ℕ) (hAg : Ag ≤ DvC) (hcGx : cGx ≤ cGg + cGt) (hBGv : BG = cGx * req.n ^ Ag)
    (h Q m pr : ℕ) (hh : 1 ≤ h)
    (hfit : CoefFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0))
    (cN : ℕ)
    (hhQ : h + Q + m + pr ≤ cN * (((gate0 l F).budget kclk coef A a ha).psiOf req.n + 1) * (req.n + 1) ^ DN)
    (hCD : 1 ≤ F.CD) :
    2 * callCost (wr5 l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha Gs sA wA cA) DvC (CvF (gate0 l F).row.cr)
      (gate0 l F).alg ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates req.word
      h Q m pr BG (cGs (gate0 l F).row.cr * classBound EGs .preprocessing req.n
        (((gate0 l F).budget kclk coef A a ha).kOf req.n) (((gate0 l F).budget kclk coef A a ha).psiOf req.n))
      (2 * (GeoFront.frontCost req.word req.n PrimT.FlipsPack.flD (PrimT.FlipsPack.flCv (gate0 l F).row.cr) +
        PrimT.Flips.flipsCost req ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr) + 2) +
      2 ≤ cWF l cN (gate0 l F).row.cr * classBound (EW3 l DN) .preprocessing req.n
        (((gate0 l F).budget kclk coef A a ha).kOf req.n) (((gate0 l F).budget kclk coef A a ha).psiOf req.n) := by
  set k := ((gate0 l F).budget kclk coef A a ha).kOf req.n with hk
  set ψ := ((gate0 l F).budget kclk coef A a ha).psiOf req.n with hψ
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := omega_factsD req.n k ψ DN
  set Ω := 2 ^ k * (req.n + 1) ^ (D0 + DN) * (ψ + 1) with hΩ
  have o4' : ∀ e, e ≤ D0 → (req.n + 1) ^ e ≤ Ω := o4
  have o5' : ∀ e, e ≤ D0 → 2 ^ k * (req.n + 1) ^ e ≤ Ω := o5
  -- the base sizes
  have sw : req.word.length ≤ PrimT.GeoPack.cW * Ω := by
    have a1 := PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha req hcall
    have a2 := PrimT.FlipsPack.word_le req.n
    have a3 := Nat.mul_le_mul_left PrimT.GeoPack.cW (o4' _ (le_of_lt dW_lt))
    omega
  have sh : h + Q + m + pr ≤ cN * Ω := le_trans hhQ (by rw [mul_assoc]; exact Nat.mul_le_mul_left _ o6)
  have sG : BG ≤ (cGg + cGt) * Ω := by
    rw [hBGv]
    exact Nat.mul_le_mul hcGx (le_trans (Nat.pow_le_pow_left (by omega) _)
      (o4' _ (le_trans hAg (le_of_lt DvC_lt))))
  have sS : cGs (gate0 l F).row.cr * classBound EGs .preprocessing req.n k ψ ≤ cGs (gate0 l F).row.cr * Ω := by
    unfold EGs; rw [classBound_EGp]
    exact Nat.mul_le_mul_left _ (le_trans (Nat.pow_le_pow_left (by omega) _)
      (o4' _ (le_trans geoD_le (le_of_lt DvC_lt))))
  have sF : 2 * (GeoFront.frontCost req.word req.n PrimT.FlipsPack.flD (PrimT.FlipsPack.flCv (gate0 l F).row.cr) +
      PrimT.Flips.flipsCost req ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr) + 2 ≤
      PrimT.FlipsPack.flipsC (gate0 l F).row.cr * Ω := by
    have hk2 : k = 2 * (((callInputs l F kclk coef A a ha).starParams req.n hs).s *
        (((callInputs l F kclk coef A a ha).starParams req.n hs).r / 2)) := by
      rw [PrimT.FlipsPack.kh_two]; rfl
    have c1 := PrimT.FlipsPack.cost_poly req ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr
      (PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha req hcall) hcall.2.2.2.2.1.1 hcall.2.2.2.2.1.2
    rw [← hk2] at c1
    have c2 : 2 ^ k * (PrimT.FlipsPack.flipsC (gate0 l F).row.cr * (req.n + 1) ^ PrimT.FlipsPack.flipsD) =
        PrimT.FlipsPack.flipsC (gate0 l F).row.cr * (2 ^ k * (req.n + 1) ^ PrimT.FlipsPack.flipsD) := by ring
    have c3 := Nat.mul_le_mul_left (PrimT.FlipsPack.flipsC (gate0 l F).row.cr) (o5' _ (le_of_lt flipsD_lt))
    exact le_trans c1 (c2 ▸ c3)
  have sV : UnaryCalc.value DvC (CvF (gate0 l F).row.cr) req.n ≤ CvF (gate0 l F).row.cr * Ω :=
    Nat.mul_le_mul_left _ (o4' _ (le_of_lt DvC_lt))
  have sC : CvF (gate0 l F).row.cr ≤ CvF (gate0 l F).row.cr * Ω := Nat.le_mul_of_pos_right _ (by omega)
  -- the size
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = req.word.length + req.n + (h + Q + m + pr) + BG +
      cGs (gate0 l F).row.cr * classBound EGs .preprocessing req.n k ψ +
      (2 * (GeoFront.frontCost req.word req.n PrimT.FlipsPack.flD (PrimT.FlipsPack.flCv (gate0 l F).row.cr) +
        PrimT.Flips.flipsCost req ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr) + 2) +
      UnaryCalc.value DvC (CvF (gate0 l F).row.cr) req.n + CvF (gate0 l F).row.cr + 1 := ⟨_, rfl⟩
  have hsum : PrimT.GeoPack.cW * Ω + Ω + cN * Ω + (cGg + cGt) * Ω + cGs (gate0 l F).row.cr * Ω +
      PrimT.FlipsPack.flipsC (gate0 l F).row.cr * Ω + CvF (gate0 l F).row.cr * Ω + CvF (gate0 l F).row.cr * Ω + Ω =
      KF cN (gate0 l F).row.cr * Ω := by unfold KF; ring
  have hSK : S0 ≤ KF cN (gate0 l F).row.cr * Ω := by
    rw [← hsum, hS0]; omega
  have c1 := call_cost_le l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha Gs sA wA cA DvC (CvF (gate0 l F).row.cr)
    req hcall hs gates BG hG h Q m pr hh hfit S0 (by omega) (by omega) (by omega) (by omega)
    (by show cGs (gate0 l F).row.cr * classBound EGs .preprocessing req.n k ψ ≤ S0; omega) (by omega) (by omega)
    (by omega)
  -- the load floor
  have hL : req.n + 2 ≤ 2 ^ Nat.clog 2 (req.n + 2) := Nat.le_pow_clog (by norm_num) _
  have hkL : k + Nat.clog 2 (req.n + 2) ≤ ψ := by
    have e : ψ = loadPsi F.CD k (Nat.clog 2 (req.n + 2))
        (((gate0 l F).budget kclk coef A a ha).capOf .thr req.n) (((gate0 l F).budget kclk coef A a ha).capOf .sym req.n) :=
      rfl
    rw [e]
    exact UnionMachine.PreProof.kL_le_loadPsi F.CD _ _ _ _ hCD
  have c3 := size_leD req.n k ψ (Nat.clog 2 (req.n + 2)) (KF cN (gate0 l F).row.cr) S0
    (dGm (Classical.choice l.eightSources.decomposition) DvC) (D0 + DN) hkL hL hSK
  have c2 := Gm_le (Classical.choice l.eightSources.decomposition) DvC S0
  calc _ ≤ Gm (Classical.choice l.eightSources.decomposition) DvC S0 := c1
    _ ≤ cGm (Classical.choice l.eightSources.decomposition) DvC *
        (S0 + 1) ^ dGm (Classical.choice l.eightSources.decomposition) DvC := c2
    _ ≤ cGm (Classical.choice l.eightSources.decomposition) DvC *
        ((KF cN (gate0 l F).row.cr + 1) ^ dGm (Classical.choice l.eightSources.decomposition) DvC *
          2 ^ ((D0 + DN + 2) * dGm (Classical.choice l.eightSources.decomposition) DvC * ψ)) := Nat.mul_le_mul_left _ c3
    _ = cWF l cN (gate0 l F).row.cr * classBound (EW3 l DN) .preprocessing req.n k ψ := by
        unfold cWF EW3; rw [classBound_EWc]; ring

end NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
