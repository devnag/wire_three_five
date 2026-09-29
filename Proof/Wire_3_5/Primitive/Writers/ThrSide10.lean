import Proof.Wire_3_5.Primitive.Writers.ThrSide9

/-! # c4 THR block, piece 6 part 10: one THR child's steps and the pad (`hcost`, `hR`)

The THR twins of the SymCost4 (`symHcost_of`) and SymCost5 (`symHR`), on the generic cores (RULING):
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
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC cDa one_le_L n2_le_L kh_two pow_mono_mul kL_le_U efOf coOf
  lt_pow_self' two_dRow_le bnOf kch_pow kch_exp symHC symDAc eXOf symKch symKn cmpCost_eq polyN_le kL_mul_le L2_mul_le)

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
variable (l : Literals) (F : GateFree l)

/-- **`hcost` at a THR call** (ThrEAt3's child step bound at `K = symKn c`, `K_ch = symKch`), under the THR floors. -/
theorem thrHcost (c : SymC) (wa : WilliamsAlgorithm) (hc : ThrHpreC l F.filterErrDeg (gate0 l F).alg c)
    (hCDo : occCDT (gate0 l F).alg c (A1T l F.filterErrDeg) (10 * CallIndex.algX l + 32) ≤ F.CD)
    (hCDq : 16 * thrC1 (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) (10 * CallIndex.algX l + 32)
      (dDT l F.filterErrDeg) ≤ F.CD)
    (hCDh : symHC c.dC (cDa (gate0 l F).alg + cmT l) c.dQ c.dD (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi)
    (hdA : symDAc c.eH c.eP c.dH c.dP (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) ≤ c.dA) (hdC : 12 * c.dT ≤ c.dC)
    (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request), p.length < 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell →
      MatrixScoreBatch.word r = Req.reqWord (PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs)) (((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) + 1)
        (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0).P.width (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams n hs))
        (Req.c3v2Ref (gate0 l F).alg (PrimT.C4Child.chR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1) (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (p ++ [b]))) →
      PrimT.C4Child.coreCost wa (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
        ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 0) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1) (symKn c n) (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (p ++ [b]) r ≤
        symKch l F c n := by
  intro p b r hp hw
  have hL1 := one_le_L n
  have hn2 := n2_le_L n
  have hkh := kh_two l F kclk coef A a ha hs
  have hQ1 := hQ_thr l F kclk coef A a ha Cs hs
  have hQp := hQp_thr l F c (by have := hc.dP2; omega) hc.eP2 kclk coef A a ha ha' Cs carriers translation hcall hs
  have hfx := thrFix_le l F c kclk coef A a ha ha' Cs carriers translation hcall hs
  have hq6 := thrQ_of l F c hCDq hcpsi hdC kclk coef A a ha ha' Cs carriers translation hcall hs
  have hnT := thrNT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hell := thrEll_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hdr := two_dRow_le ((callInputs l F kclk coef A a ha).starParams n hs)
  have hK : ((gate0 l F).budget kclk coef A a ha).kOf n = ((callInputs l F kclk coef A a ha).starParams n hs).r * ((callInputs l F kclk coef A a ha).starParams n hs).s := rfl
  have hrn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
  rw [← hK, hrn] at hdr
  have hsy := loadThr_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hLL := L2_mul_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hkL := kL_mul_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hψ : ((gate0 l F).budget kclk coef A a ha).psiOf n = loadPsi F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n) := rfl
  rw [← hψ] at hsy hLL hkL
  have hfits := hcall.2.2.2.2.2.2.pre
  have hcp : 1 ≤ (gate0 l F).E.cpsi := hcpsi
  have hn : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤ n := by
    have : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤ (gate0 l F).E.cpsi * ((gate0 l F).budget kclk coef A a ha).psiOf n := Nat.le_mul_of_pos_left _ hcp
    exact this.trans (le_trans (Nat.le_add_right _ _) hfits)
  have hsy' : F.CD * F.CD * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) ≤
      ((gate0 l F).budget kclk coef A a ha).psiOf n := by rw [sT_add]; exact hsy
  have hex := kch_exp n (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2))) F.CD (((gate0 l F).budget kclk coef A a ha).psiOf n)
    c.dC c.dA (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg)
    (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) hL1 hsy' hLL hkL hn hCDh hdA
  have hKU : (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) ≤ ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) := kL_le_U (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2))) hL1
  -- the call's numbers against `e_X`
  have hl : (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell ≤ (eXOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) := by
    have a1 : (eQT l F.filterErrDeg + 2) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) ≤
        (eNT l F.filterErrDeg + 8 * eQT l F.filterErrDeg + 24 + (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD)) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) :=
      Nat.mul_le_mul (by omega) hKU
    unfold eXOf; omega
  have hkh' : (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).kh ≤ (eXOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) := by
    show SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) ≤ _
    have a1 : (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) ≤ (eNT l F.filterErrDeg + 8 * eQT l F.filterErrDeg + 24 + (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD)) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) :=
      hKU.trans (Nat.le_mul_of_pos_left _ (by omega))
    unfold eXOf; omega
  have hnn : (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * 2 ^ (8 + 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell + 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).kh) ≤ 2 ^ (eXOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) := by
    have a1 : (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * 2 ^ (8 + 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell + 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).kh) ≤
        2 ^ (eNT l F.filterErrDeg * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) * 2 ^ (8 + 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell + 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).kh) :=
      Nat.mul_le_mul_right _ hnT
    refine a1.trans ?_
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    have hkh2 : (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).kh ≤ ((gate0 l F).budget kclk coef A a ha).kOf n := by show SeedFix.callKh _ ≤ _; omega
    have a2 : (eNT l F.filterErrDeg + 8 * eQT l F.filterErrDeg + 24) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) ≤
        (eNT l F.filterErrDeg + 8 * eQT l F.filterErrDeg + 24) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) := Nat.mul_le_mul_left _ hKU
    have e1 : (eNT l F.filterErrDeg + 8 * eQT l F.filterErrDeg + 24) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) =
        eNT l F.filterErrDeg * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) + 8 * ((eQT l F.filterErrDeg + 2) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) + 8 * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) := by
      ring
    have e2 : (eNT l F.filterErrDeg + 8 * eQT l F.filterErrDeg + 24 + (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD)) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) =
        (eNT l F.filterErrDeg + 8 * eQT l F.filterErrDeg + 24) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) + (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) := by ring
    unfold eXOf; omega
  have hFX : 8 + 3 * (efOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) ≤ (eXOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) := by unfold eXOf; omega
  have hOX : (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) + 1 ≤ (eXOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) := by
    have e2 : (eNT l F.filterErrDeg + 8 * eQT l F.filterErrDeg + 24 + (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD)) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) =
        (eNT l F.filterErrDeg + 8 * eQT l F.filterErrDeg + 24) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) + (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) := by ring
    unfold eXOf; omega
  -- the capacity side
  have hG : PrimT.C4Grp.qG (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1) (PrimT.C4Grp.bsz (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation))
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 0) (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) + 1 ≤ 2 ^ (n / 16 + c.dC * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) := by
    have h1 : PrimT.C4Grp.qG (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1) (PrimT.C4Grp.bsz (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation))
        ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 0) (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) + 1 ≤ (PrimT.C4Grp.qG (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1)
        (PrimT.C4Grp.bsz (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 0) (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    have h2 : (PrimT.C4Grp.qG (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1)
        (PrimT.C4Grp.bsz (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 0) (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) + 1) ^ 6 ≤ FinalPass.EnumCap.capC *
        (PrimT.C4Grp.qG (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1)
        (PrimT.C4Grp.bsz (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 0) (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) + 1) ^ 6 :=
      Nat.le_mul_of_pos_left _ (by unfold FinalPass.EnumCap.capC; norm_num)
    exact h1.trans (h2.trans hq6)
  have hT : ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 0) ≤ 2 ^ (n / 16 + c.dC * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) := by
    refine le_trans ?_ (lt_pow_self' _)
    show c.dT * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) ≤ _
    have a1 : c.dT ≤ c.dC := by omega
    have := Nat.mul_le_mul_right (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) a1
    omega
  have hC : ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1) ≤ 2 ^ (n / 16 + c.dC * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) := le_rfl
  have hKn : symKn c n ≤ 2 ^ (n / 16 + c.dC * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) := le_rfl
  -- the pad's table term
  have hPr : PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) + ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) + 2 ≤ 2 ^ (c.dP + 2 + (c.eP + 1) * Nat.clog 2 (n + 2)) := by
    have a1 : ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) ≤ 2 ^ (c.dP + c.eP * Nat.clog 2 (n + 2)) := polyN_le c.dP c.eP n (Nat.clog 2 (n + 2)) hn2
    have a2 : PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) ≤ 2 ^ Nat.clog 2 (n + 2) := by omega
    have a3 : (2 : ℕ) ^ (c.dP + 2 + (c.eP + 1) * Nat.clog 2 (n + 2)) = 4 * 2 ^ (c.dP + c.eP * Nat.clog 2 (n + 2) + Nat.clog 2 (n + 2)) := by
      rw [show c.dP + 2 + (c.eP + 1) * Nat.clog 2 (n + 2) = (c.dP + c.eP * Nat.clog 2 (n + 2) + Nat.clog 2 (n + 2)) + 2 by ring, pow_add]; ring
    have a4 : (2 : ℕ) ^ (c.dP + c.eP * Nat.clog 2 (n + 2)) ≤ 2 ^ (c.dP + c.eP * Nat.clog 2 (n + 2) + Nat.clog 2 (n + 2)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have a5 : (2 : ℕ) ^ Nat.clog 2 (n + 2) ≤ 2 ^ (c.dP + c.eP * Nat.clog 2 (n + 2) + Nat.clog 2 (n + 2)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [a3]
    omega
  have hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell →
      (PrimT.C4Child.chR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1) (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (p ++ [b])).Pre (gate0 l F).alg := fun p b _ =>
    hpre_thr l F c hc hCDo hcpsi kclk coef A a ha ha' Cs carriers translation hcall hs (p ++ [b])
  have hO : ∀ (p : List Bool) (b : Bool), p.length < 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell →
      (PrimT.C4Child.chR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1) (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (p ++ [b])).occBoundP (gate0 l F).alg ≤ 2 ^ ((coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2)))) := fun p b _ =>
    thrOcc_le l F c kclk coef A a ha ha' Cs carriers translation hcall hs (p ++ [b])
  have hpm : ∀ V ∈ (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation), ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1 := fun V hV t ht =>
    Or.inl (BShape.thr_coef_one (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation V hV t ht)
  exact hcost_pad wa (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 0) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (carriers.length + 1) (symKn c n) (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (n / 16 + c.dC * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) (eXOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) ((coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2)))) (efOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2)))
    (c.dP + 2 + (c.eP + 1) * Nat.clog 2 (n + 2)) (n - ((gate0 l F).budget kclk coef A a ha).kOf n) c.dA (Nat.clog 2 (n + 2)) hpm hQ1 hQp hpre hO hfx hG hT hC hKn
    hl hkh' hnn hFX hOX hdr hPr hex.1 hex.2.1 hex.2.2 p b r hp hw

/-- **The pad over the THR family's cell** (ThrEAt3's `hR` at the explicit cell cost). -/
theorem thrHR (c : SymC) (wa : WilliamsAlgorithm) (hCDh : symHC c.dC (cDa (gate0 l F).alg + cmT l) c.dQ c.dD (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi)
    (hdA : symDAc c.eH c.eP c.dH c.dP (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) ≤ c.dA)
    (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (2 * symKch l F c n + 2) + 1 + ((2 * symKch l F c n + 2) + 1 +
      (2 * PrimT.C4Loop.cmpCost (PrimT.C4Child.chW (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0))
        (List.replicate (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) false) + 2)) + 1 ≤ 2 ^ ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6) := by
  have hL1 := one_le_L n
  have hkh := kh_two l F kclk coef A a ha hs
  have hfx := thrFix_le l F c kclk coef A a ha ha' Cs carriers translation hcall hs
  have hell := thrEll_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hsy := loadThr_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hLL := L2_mul_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hkL := kL_mul_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hψ : ((gate0 l F).budget kclk coef A a ha).psiOf n = loadPsi F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n) := rfl
  rw [← hψ] at hsy hLL hkL
  have hfits := hcall.2.2.2.2.2.2.pre
  have hcp : 1 ≤ (gate0 l F).E.cpsi := hcpsi
  have hn : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤ n := by
    have : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤ (gate0 l F).E.cpsi * ((gate0 l F).budget kclk coef A a ha).psiOf n := Nat.le_mul_of_pos_left _ hcp
    exact this.trans (le_trans (Nat.le_add_right _ _) hfits)
  have hsy' : F.CD * F.CD * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) ≤
      ((gate0 l F).budget kclk coef A a ha).psiOf n := by rw [sT_add]; exact hsy
  have hex := kch_exp n (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2))) F.CD (((gate0 l F).budget kclk coef A a ha).psiOf n)
    c.dC c.dA (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg)
    (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) hL1 hsy' hLL hkL hn hCDh hdA
  have hKU : (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) ≤ ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) := kL_le_U (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2))) hL1
  have hF : FinalPass.EnumCap.fixB (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) ≤ 2 ^ (efOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) :=
    le_trans (Nat.le_add_right _ _) hfx
  have hl : (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell ≤ 2 ^ (eXOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) := by
    refine le_trans ?_ (lt_pow_self' _)
    have a1 : (eQT l F.filterErrDeg + 2) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) ≤
        (eNT l F.filterErrDeg + 8 * eQT l F.filterErrDeg + 24 + (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD)) * ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) :=
      Nat.mul_le_mul (by omega) hKU
    unfold eXOf; omega
  have hFX : (efOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) ≤ (eXOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) := by unfold eXOf; omega
  have hE : (eXOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) + 13 ≤ n - ((gate0 l F).budget kclk coef A a ha).kOf n + c.dA * Nat.clog 2 (n + 2) := by
    have := hex.1
    unfold eXOf; omega
  have hρ : n - ((gate0 l F).budget kclk coef A a ha).kOf n + c.dA * Nat.clog 2 (n + 2) ≤ ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6) := by
    show _ ≤ max (n - (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + c.dA * Nat.clog 2 (n + 2))
      (c.dR * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)))
    have : SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) = ((gate0 l F).budget kclk coef A a ha).kOf n := by omega
    rw [this]
    exact le_max_left _ _
  exact hr_pad (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell (symKch l F c n) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6) (efOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2))) (eXOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2)))
    (n - ((gate0 l F).budget kclk coef A a ha).kOf n + c.dA * Nat.clog 2 (n + 2)) hF hl hFX hE rfl hρ

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
