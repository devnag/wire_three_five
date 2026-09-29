import Proof.Wire_3_5.Primitive.SeedFix.ThrTB5

/-! # THRTAIL T-B, part 6: the THR writer's run at a call

The THR writer `thrM` = the v4 shell `shellMGH4` over the v4 data stage `S`, the unit machine `U` (THRU4) and
T-A's dimension stage `thrDimStageG l F K_L K_f` (`K_L = kLT l f_e D₀`, `K_f = D₀ + 1`), the scrub capacity
`(dSh D₀, cSh D₀ C₀ C_L)`, the data width `(dT2 l D₀, cT2 l F C₀)`, the fill `(D_nG, K_n)`, the loop `(1, C_L)`.
**`thr_run`**: at every THR call, from `frame thrCallW`, within `128·K²·Y^E·Y^E` (`Y = 2^{m_T} + 1`, `costG_le`),
the output is the THR tape (`shell_runH4`; the unit's `UnitOK` from `U.ok` at `cap = need(meas) + b`;
`ThrTail.thr_loop_tape` at `b = C_L·Y ≥ thrTOT`).

* `thrM`, `eT`, `kTB`, `budT`; **`thr_run`**.

Paper quantity of the main type: the THR tape `thrTape` (C4's `BAT` word, P3:3011-3016) written within
`2^{O(m_T)}` steps. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.RepairOrdinary

section Writer
variable (l : Literals) (F : GateFree l) (fe D0 C0 kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
  (S : ThrData.ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a ha).D
    (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap))
  (U : ThrUnit.ThrUnitSpec4 l F)

/-- T-A's dimension stage at the THR writer's constants. -/
noncomputable abbrev dimT : ThrDim.ThrDimStage l F (kLT l fe D0) (kFT D0) (ThrDimB.DnG l) (ThrDimB.DcG l) :=
  ThrDimB.thrDimStageG l F (kLT l fe D0) (kFT D0)

/-- **The THR writer's machine.** -/
noncomputable def thrM :=
  ShellT.shellMGH4 S U.x U.U (dSh D0) (cSh D0 C0 (cLT l F)) (dT2 l D0) (cT2 l F C0) (ThrDimB.DnG l)
    (dimT l F fe D0).Kn 1 (cLT l F) (dimT l F fe D0).M2

/-- The budget's exponent (from `(l, D₀)`). -/
noncomputable def eT : ℕ := dT2 l D0 * D0 + ThrDimB.DnG l * ThrDimB.DcG l + dSh D0 + dT2 l D0 + ThrDimB.DnG l + 3

/-- The budget's coefficient (from `(F, f_e, D₀, C₀)`). -/
noncomputable def kTB : ℕ :=
  kShell (dSh D0) (cSh D0 C0 (cLT l F)) (dT2 l D0) (cT2 l F C0) (ThrDimB.DnG l) (dimT l F fe D0).Kn 1 (cLT l F) +
    C0 * (3 * cT2 l F C0 + 1) ^ D0 + (dimT l F fe D0).Kc * ((dimT l F fe D0).Kn + 1) ^ ThrDimB.DcG l +
    cSh D0 C0 (cLT l F)

/-- The monomial bound at `Y ≥ n + 1`. -/
theorem mono_Y {X c d Y E n : ℕ} (hX : X ≤ c * (n + 1) ^ d) (hn : n + 1 ≤ Y) (hd : d ≤ E) : X ≤ c * Y ^ E :=
  hX.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hn d).trans (Nat.pow_le_pow_right (by omega) hd)))

/-- The data stage's cost, arithmetic: `C_c(3V + n + 1)^{D_c} ≤ K·Y^E`. -/
theorem cc_arith (cost Cc Dc V n Y D0 C0 c2 d2 E K : ℕ) (hc : cost ≤ Cc * (V + n + V + V + 1) ^ Dc)
    (hCc : Cc ≤ C0) (hDc : Dc ≤ D0) (hV : V ≤ c2 * Y ^ d2) (hnY : n + 1 ≤ Y ^ d2) (hY : 1 ≤ Y) (hE : d2 * D0 ≤ E)
    (hK : C0 * (3 * c2 + 1) ^ D0 ≤ K) : cost ≤ K * Y ^ E := by
  obtain ⟨Z, hZ⟩ : ∃ x, x = Y ^ d2 := ⟨_, rfl⟩
  rw [← hZ] at hV hnY
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact Nat.one_le_pow _ _ hY
  have hb : V + n + V + V + 1 ≤ (3 * c2 + 1) * Z := by
    have e : (3 * c2 + 1) * Z = 3 * (c2 * Z) + Z := by ring
    omega
  have hb1 : 1 ≤ (3 * c2 + 1) * Z := by nlinarith
  have hp : (V + n + V + V + 1) ^ Dc ≤ (3 * c2 + 1) ^ D0 * Y ^ (d2 * D0) := by
    calc (V + n + V + V + 1) ^ Dc ≤ ((3 * c2 + 1) * Z) ^ Dc := Nat.pow_le_pow_left hb _
      _ ≤ ((3 * c2 + 1) * Z) ^ D0 := Nat.pow_le_pow_right hb1 hDc
      _ = (3 * c2 + 1) ^ D0 * Y ^ (d2 * D0) := by rw [mul_pow, hZ, ← pow_mul]
  calc cost ≤ Cc * (V + n + V + V + 1) ^ Dc := hc
    _ ≤ C0 * ((3 * c2 + 1) ^ D0 * Y ^ (d2 * D0)) := Nat.mul_le_mul hCc hp
    _ = C0 * (3 * c2 + 1) ^ D0 * Y ^ (d2 * D0) := by ring
    _ ≤ K * Y ^ E := Nat.mul_le_mul hK (Nat.pow_le_pow_right hY hE)

/-- **The data stage's cost at the master bound.** -/
theorem cc_le (hSD : S.Dc3 ≤ D0) (hSC : S.Cc3 ≤ C0) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation)) (Y : ℕ) (hn : n + 1 ≤ Y) :
    S.cost3 a' Cs carriers (UnaryCalc.value (dT2 l D0) (cT2 l F C0) n) (UnaryCalc.value (dT2 l D0) (cT2 l F C0) n) ≤
      kTB l F fe D0 C0 * Y ^ eT l D0 := by
  obtain ⟨h1, h2, h3, -, -, -, -, -, -, h10, h11⟩ := C4GateSym.thr_data_hyps Cs carriers ha' hcall.2.2.2.1
    hcall.2.2.1 hcall.2.1 _ (needW_le_V l F (n := n) D0 C0)
  have hc := S.cost3_le Cs carriers (UnaryCalc.value (dT2 l D0) (cT2 l F C0) n)
    (UnaryCalc.value (dT2 l D0) (cT2 l F C0) n) (UnaryCalc.value (dT2 l D0) (cT2 l F C0) n) ha' hcall.2.2.2.1
    h1 h2 h10 h11 h3
  unfold ValidatorPolynomialDomination.PolyBounded at hc
  have hY1 : 1 ≤ Y := by omega
  have hd1 : 1 ≤ dT2 l D0 := by unfold dT2; omega
  have hnY : n + 1 ≤ Y ^ dT2 l D0 :=
    hn.trans (by calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ dT2 l D0 := Nat.pow_le_pow_right hY1 hd1)
  have hVY : UnaryCalc.value (dT2 l D0) (cT2 l F C0) n ≤ cT2 l F C0 * Y ^ dT2 l D0 := mono_Y (le_refl _) hn le_rfl
  have hE : dT2 l D0 * D0 ≤ eT l D0 := by unfold eT; omega
  have hK : C0 * (3 * cT2 l F C0 + 1) ^ D0 ≤ kTB l F fe D0 C0 := by unfold kTB; omega
  exact cc_arith _ _ _ _ n Y D0 C0 _ _ _ _ hc hSC hSD hVY hnY hY1 hE hK

end Writer

section Dim
variable (l : Literals) (F : GateFree l) (fe D0 C0 : ℕ)

/-- **The dimension stage's cost at the master bound.** -/
theorem c2_le' (P : Shared.StarParams) (Y : ℕ) (hn : P.n + 1 ≤ Y) :
    (dimT l F fe D0).c2 (UnaryCalc.value (ThrDimB.DnG l) (dimT l F fe D0).Kn P.n) P ≤
      ((dimT l F fe D0).Kc * ((dimT l F fe D0).Kn + 1) ^ ThrDimB.DcG l) * Y ^ (ThrDimB.DnG l * ThrDimB.DcG l) := by
  have h := (dimT l F fe D0).c2_le (UnaryCalc.value (ThrDimB.DnG l) (dimT l F fe D0).Kn P.n) P
  have hY1 : 1 ≤ Y := by omega
  have hW : UnaryCalc.value (ThrDimB.DnG l) (dimT l F fe D0).Kn P.n + P.n + 1 ≤
      ((dimT l F fe D0).Kn + 1) * Y ^ ThrDimB.DnG l := by
    unfold UnaryCalc.value
    have a1 : (P.n + 1) ^ ThrDimB.DnG l ≤ Y ^ ThrDimB.DnG l := Nat.pow_le_pow_left hn _
    have a2 : P.n + 1 ≤ Y ^ ThrDimB.DnG l := by
      have h0 : 1 ≤ ThrDimB.DnG l := by unfold ThrDimB.DnG; omega
      calc P.n + 1 ≤ Y := hn
        _ = Y ^ 1 := (pow_one Y).symm
        _ ≤ Y ^ ThrDimB.DnG l := Nat.pow_le_pow_right hY1 h0
    have e : ((dimT l F fe D0).Kn + 1) * Y ^ ThrDimB.DnG l = (dimT l F fe D0).Kn * Y ^ ThrDimB.DnG l + Y ^ ThrDimB.DnG l := by
      ring
    have := Nat.mul_le_mul_left (dimT l F fe D0).Kn a1
    omega
  calc (dimT l F fe D0).c2 (UnaryCalc.value (ThrDimB.DnG l) (dimT l F fe D0).Kn P.n) P
      ≤ (dimT l F fe D0).Kc * (UnaryCalc.value (ThrDimB.DnG l) (dimT l F fe D0).Kn P.n + P.n + 1) ^ ThrDimB.DcG l := h
    _ ≤ (dimT l F fe D0).Kc * (((dimT l F fe D0).Kn + 1) * Y ^ ThrDimB.DnG l) ^ ThrDimB.DcG l :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW _)
    _ = ((dimT l F fe D0).Kc * ((dimT l F fe D0).Kn + 1) ^ ThrDimB.DcG l) * Y ^ (ThrDimB.DnG l * ThrDimB.DcG l) := by
        rw [mul_pow, ← pow_mul]; ring

end Dim

end NearCubicWires.WireExponent3_5.PrimT.ThrTB
