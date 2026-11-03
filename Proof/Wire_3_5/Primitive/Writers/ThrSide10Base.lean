import Proof.Wire_3_5.Primitive.Writers.ThrSide9Base

/-! # PA2 c4 THR block, piece 6 part 10: one THR child's steps and the pad (`hcost`, `hR`)

The THR twins of the SymCost4 (`symHcost_of`) and SymCost5 (`symHR`), on the generic cores:
* **`hcost_pad`** (generic in the request, the seed parameters and the batch): EnumCap's `hcost_of` at
  `q = 2^{e_C}·2^{e_X}`, `𝒮' ≤ 2^{e_O}`, `B_n = bnOf`, then `kch_pow`: one child's steps below `2^{E₁ + d_A L − 4}`;
* **`hr_pad`** (generic in the request): the loop cell `4K_ch + 146W + 80ℓ + 79` of a child family below `2^ρ`;
* **`thrHcost`** (ThrEAt3's `hcost` at `K_ch = symKch`, P3:3011-3016, 1905-1906, 3098-3100) and **`thrHR`** (ThrEAt3's
  pad at the family's explicit cell cost), under the THR floors `symHC(d_C, cDa + c_m, …, c_O^T) ≤ C_D` and
  `symDAc ≤ d_A`, at the THR load `U = (k+L)²(sT + L) = (k+L)²(⌊√(B_T L)⌋ + L²)`.

Paper quantities of the main types: one THR child's step count and the THR loop cell's steps against the pad. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC cDa one_le_L n2_le_L pow_mono_mul kL_le_U efOf coOf lt_pow_self' two_dRow_le bnOf kch_pow kch_exp symHC symDAc eXOf symKn cmpCost_eq polyN_le kL_mul_le L2_mul_le)

/-- **One child's steps below `2^{E₁ + d_A L − 4}`**, generic in the request `R0`, the seed parameters and the batch
(EnumCap's `hcost_of` at `q = 2^{e_C}·2^{e_X}`, `O = 2^{e_O}`, `B_n = bnOf`, then `kch_pow`). -/
theorem hcost_pad (wa : WilliamsAlgorithm) (a : DecompositionAlgorithm) (R0 : Req.C3Req) (P : Sampler.SeedParams)
    (TWd Cap nT Rn K : ℕ) (batch : List SeedFix.SExpr) (eC eX eO eF ePr E1 dA L : ℕ)
    (hpm : ∀ V ∈ batch, ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1) (hQ1 : 1 ≤ P.Q) (hQp : R0.P.Q ≤ R0.p)
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * P.ell →
      (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b])).Pre a)
    (hO : ∀ (p : List Bool) (b : Bool), p.length < 8 * P.ell →
      (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b])).occBoundP a ≤ 2 ^ eO)
    (hFB : FinalPass.EnumCap.fixB a R0 + bnOf a R0 ≤ 2 ^ eF)
    (hG : PrimT.C4Grp.qG P nT Rn (PrimT.C4Grp.bsz batch) TWd (8 * P.ell) + 1 ≤ 2 ^ eC)
    (hT : TWd ≤ 2 ^ eC) (hC : Cap ≤ 2 ^ eC) (hK : K ≤ 2 ^ eC)
    (hl : P.ell ≤ eX) (hkh : P.kh ≤ eX) (hn : nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) ≤ 2 ^ eX)
    (hFX : 8 + 3 * eF ≤ eX) (hOX : eO + 1 ≤ eX)
    (hdR : 2 * R0.dRow ≤ E1 + 1) (hPr : R0.dRow + R0.p + 2 ≤ 2 ^ ePr)
    (h1 : 3 * (eC + eX) + 27 ≤ E1 + dA * L) (h2 : 8 * eO + 32 * eF + 8 * eC + 94 ≤ E1 + dA * L)
    (h3 : CompetitorCountTable.coefficient wa + 1034023 + CompetitorCrossScheduler.exponent wa * ePr ≤ dA * L) :
    ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request), p.length < 8 * P.ell →
      MatrixScoreBatch.word r = Req.reqWord R0.dRow (R0.p + 1) R0.P.width R0.cols
        (Req.c3v2Ref a (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b]))) →
      PrimT.C4Child.coreCost wa a R0 P TWd Cap nT Rn K batch (p ++ [b]) r ≤ 2 ^ (E1 + dA * L - 4) := by
  intro p b r hp hw
  have hF : FinalPass.EnumCap.fixB a R0 ≤ 2 ^ eF := le_trans (Nat.le_add_right _ _) hFB
  have hBn : bnOf a R0 ≤ 2 ^ eF := le_trans (Nat.le_add_left _ _) hFB
  have hfp : FinalPass.EnumCap.fixB a R0 = R0.P.Q + (R0.D a).flatten.length + (R0.D a).length + R0.m + R0.P.h +
      R0.p + R0.P.width + R0.dRow + R0.cols.length + 1 := rfl
  have hbn : bnOf a R0 = R0.p + R0.P.width + (Pool.poolChildren a R0.P.gates R0.P.flips).length + R0.P.h + R0.P.Q +
      R0.d + 1 := rfl
  have hEX : (2 : ℕ) ^ eF ≤ 2 ^ eX := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1 : ∀ v, v ≤ 2 ^ eX → v ≤ 2 ^ eC * 2 ^ eX := fun v hv =>
    hv.trans (Nat.le_mul_of_pos_left _ Nat.one_le_two_pow)
  have hq2 : ∀ v, v ≤ 2 ^ eC → v ≤ 2 ^ eC * 2 ^ eX := fun v hv =>
    hv.trans (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)
  have tfix : 256 * FinalPass.EnumCap.fixB a R0 ^ 3 ≤ 2 ^ eC * 2 ^ eX := by
    refine hq1 _ ?_
    calc 256 * FinalPass.EnumCap.fixB a R0 ^ 3 ≤ 2 ^ 8 * 2 ^ (3 * eF) :=
          Nat.mul_le_mul (by norm_num) (pow_mono_mul 3 hF)
      _ = 2 ^ (8 + 3 * eF) := by rw [pow_add]
      _ ≤ 2 ^ eX := Nat.pow_le_pow_right (by norm_num) hFX
  have tO : 2 * 2 ^ eO ≤ 2 ^ eC * 2 ^ eX := by
    refine hq1 _ ?_
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) hOX
  have hl' : P.ell ≤ 2 ^ eX := hl.trans (lt_pow_self' _)
  have hkh' : P.kh ≤ 2 ^ eX := hkh.trans (lt_pow_self' _)
  have hc0 := FinalPass.EnumCap.hcost_of wa a R0 P TWd Cap nT Rn K batch (2 ^ eC * 2 ^ eX) (2 ^ eO) (bnOf a R0)
    hpm hQ1 hQp hpre hO (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (hq1 _ hl') (hq1 _ hkh') (hq2 _ hT) (hq2 _ hC) (hq1 _ hn) (hq2 _ hK) tfix
    (hq2 _ (by omega)) (hq1 _ (by omega)) (hq1 _ (by omega)) (hq1 _ (by omega)) tO (hq1 _ (by omega)) p b r hp hw
  have hkp := kch_pow eC eX eO eF ePr E1 dA L (2 ^ eC * 2 ^ eX) (2 ^ eO) (FinalPass.EnumCap.fixB a R0) (bnOf a R0)
    (PrimT.C4Grp.qG P nT Rn (PrimT.C4Grp.bsz batch) TWd (8 * P.ell)) R0.dRow R0.p
    (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) rfl le_rfl hF hBn hG hdR hPr h1 h2 h3
  unfold FinalPass.EnumCap.tabT at hc0
  exact hc0.trans hkp

/-- **The loop cell of a child family below the pad**, generic in the request: `4K_ch + 146W + 80ℓ + 79 ≤ 2^ρ` at
`K_ch = 2^{E−4}`, `W = chW R0 ≤ 2·2^{e_F} + 4`, `ℓ ≤ 2^{e_X}`, `e_F ≤ e_X`, `e_X + 13 ≤ E ≤ ρ`. -/
theorem hr_pad (a : DecompositionAlgorithm) (R0 : Req.C3Req) (ell Kch rho eF eX E : ℕ)
    (hF : FinalPass.EnumCap.fixB a R0 ≤ 2 ^ eF) (hl : ell ≤ 2 ^ eX) (hFX : eF ≤ eX) (hE : eX + 13 ≤ E)
    (hK : Kch = 2 ^ (E - 4)) (hρ : E ≤ rho) :
    (2 * Kch + 2) + 1 + ((2 * Kch + 2) + 1 + (2 * PrimT.C4Loop.cmpCost (PrimT.C4Child.chW R0)
      (List.replicate (8 * ell) false) + 2)) + 1 ≤ 2 ^ rho := by
  have hfp : FinalPass.EnumCap.fixB a R0 = R0.P.Q + (R0.D a).flatten.length + (R0.D a).length + R0.m + R0.P.h +
      R0.p + R0.P.width + R0.dRow + R0.cols.length + 1 := rfl
  have hW : PrimT.C4Child.chW R0 ≤ 2 * 2 ^ eF + 4 := by
    show R0.P.Q + (2 * R0.dRow + 2 * (R0.p + 1) + 4) ≤ _
    omega
  have hFX' : (2 : ℕ) ^ eF ≤ 2 ^ eX := Nat.pow_le_pow_right (by norm_num) hFX
  have hX1 : 1 ≤ (2 : ℕ) ^ eX := Nat.one_le_two_pow
  have hsm : (2 : ℕ) ^ (eX + 11) ≤ 2 ^ (E - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e11 : (2 : ℕ) ^ (eX + 11) = 2048 * 2 ^ eX := by rw [pow_add]; ring
  have e4 : (2 : ℕ) ^ (E - 2) = 4 * 2 ^ (E - 4) := by
    rw [show E - 2 = (E - 4) + 2 by omega, pow_add]; ring
  have e2 : (2 : ℕ) ^ E = 4 * 2 ^ (E - 2) := by
    have h : (2 : ℕ) ^ E = 2 ^ ((E - 2) + 2) := congrArg (2 ^ ·) (by omega)
    rw [h, pow_add]; ring
  have hpad : (2 : ℕ) ^ E ≤ 2 ^ rho := Nat.pow_le_pow_right (by norm_num) hρ
  rw [cmpCost_eq, List.length_replicate, hK]
  generalize (2 : ℕ) ^ eX = X at hl hFX' hX1 e11 hsm
  generalize (2 : ℕ) ^ eF = Y at hF hW hFX'
  generalize PrimT.C4Child.chW R0 = W at hW
  generalize (2 : ℕ) ^ rho = Z at hpad
  generalize (2 : ℕ) ^ (E - 4) = A4 at e4
  generalize (2 : ℕ) ^ (E - 2) = A2 at e4 e2 hsm
  generalize (2 : ℕ) ^ E = A0 at e2 hpad
  omega

section Gate

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
