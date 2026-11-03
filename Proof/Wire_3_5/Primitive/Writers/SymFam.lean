import Lean
import Proof.Wire_3_5.Primitive.Writers.SymHelp
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SymNeed
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.SymFamBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 (SYM leaf), part 10: the SYM writer's constants and its generic budgets

The SYM writer's constants are functions of the base constants `SB` (the producers' exponents and coefficients: the
call word's `C_w(n+1)^{D_w}`, the `needW`, PA's data stage `symCc`, `symDc`, the FILTER and POP setups' needs and
bounds, `FiltPipeLe2`'s `K_f`, `D_f`, `PopPipeLe`'s `K_p`, `D_p`, the literals' `Z`, `Z_m`, `C_sp`, the schedule's `J`,
`c_X`, `K_Λ`, the gate's `capK c_r`, `c_r`, `fe`, `cMain`):

* the dimension `m_S = k + L + K_F·L² + T` (`NumsXS.mS` at `D₂' = 26`, `K₀ = 6`), `Q = 2^{m_S} + 1`; `K_F` (after `F`)
  dominates every polynomial degree of the call's sizes and the log-coefficients of `2^{seedBits}`, `2^{fbv}`, the FILTER
  row's `(L_s+2)^{D_f(fe·L+1)}` and the POP walk's `2^{D_p(L+5)}`, so every size is at most `K_A·Q` (`atomQ`);
* the data width `V = C₂(n+1)^{D₂}` (`needW`), the fill `W = C_v(n+1)^{D_v}` (**`sneed_fam`**: `NumsXS.SNeed`), the loop
  `b = K_A·Q`, the capacity `cap = K_cap·Q^{d_cap}` (the setups' needs), the scrub `R = K_r·Q^D` (`D` absolute);
* **`capNeed_of`** (CapNum's capacity conditions from one bound), the size helpers (`fbv_fam`, `exp_filter`,
  `popY_fam`), and the generic budgets of `sym_ready`'s hypotheses: **`fn_block`** (FILTER rows), **`pn_block`** (POP
  rows), **`nu_block`** (the unit), `nn_block`, `cap_block`, `p1_block`, `r_block`.

Paper quantities of the main types: the SYM dimension stage's needs at the fill (NumsXS.SNeed, the dimension
`2^{m_S}` of P3:3089-3108) and the SYM row budgets against the pipelines (prim:runtime P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline

namespace SB

end SB

/-! ## Helpers -/

/-! ## The capacity conditions of the SYM row's cap -/

theorem cEnc_le_cMain (l : Literals) : CapNum.cEnc (gateCap l) ≤ CapNum.cMain (gateCap l) .sym := by
  have hb : 1 ≤ gateBetaInv l := one_le_betaInv l
  have e1 : CapNum.cEnc (gateCap l) = 128 * gateBetaInv l ^ 2 := by
    show 32 * 2 ^ 2 * gateBetaInv l ^ 2 = 128 * gateBetaInv l ^ 2; norm_num
  have e2 : CapNum.cMain (gateCap l) .sym = 2 ^ 80 * gateBetaInv l ^ 32 := by
    show 2 ^ 80 * 1 ^ 32 * gateBetaInv l ^ 32 = 2 ^ 80 * gateBetaInv l ^ 32; norm_num
  rw [e1, e2]
  have h1 : gateBetaInv l ^ 2 ≤ gateBetaInv l ^ 32 := Nat.pow_le_pow_right hb (by norm_num)
  have h2 : (128 : ℕ) ≤ 2 ^ 80 := by norm_num
  exact Nat.mul_le_mul h2 h1

/-- **`CapNum.capM_spec`'s capacity conditions** from one bound `2^40·capK·(n+2)^{Z_m} + cMain ≤ cap`. -/
theorem capNeed_of (l : Literals) (cr n cap : ℕ)
    (h : 2 ^ 40 * (CallIndexR.capK cr * (n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
      CapNum.cMain (gateCap l) .sym ≤ cap) :
    SymDec.CapNeed (gateCap l) .sym n (Ledger.rowBr cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) cap := by
  obtain ⟨N, hNd⟩ : ∃ N, N = n + 2 := ⟨_, rfl⟩
  obtain ⟨Zm, hZm⟩ : ∃ z, z = 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32 := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K, K = CallIndexR.capK cr := ⟨_, rfl⟩
  have hnum := CallIndexR.capMain_leR l cr .sym n hNd
  have henc := CallIndexR.capEnc_leR l cr n hNd
  rw [← hNd, ← hZm, ← hKd] at h
  rw [← hZm, ← hKd] at hnum
  rw [← hKd] at henc
  have hN : 2 ≤ N := by omega
  have hK1 : 1 ≤ K := hKd ▸ CallIndexR.capK_pos cr
  have hKr : 2 * cr + 2 ≤ K := by
    rw [hKd]; unfold CallIndexR.capK; exact Nat.le_self_pow (by norm_num) _
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = K * N ^ Zm := ⟨_, rfl⟩
  have pw : ∀ d, d ≤ Zm → N ^ d ≤ N ^ Zm := fun d hd => Nat.pow_le_pow_right (by omega) hd
  have kY : ∀ x d, d ≤ Zm → x ≤ K * N ^ d → x ≤ Y := fun x d hd hx =>
    le_trans hx (hYd ▸ Nat.mul_le_mul_left _ (pw d hd))
  have hY1 : 1 ≤ Y := by rw [hYd]; exact Nat.mul_le_mul hK1 (Nat.one_le_pow _ _ (by omega))
  have hNK : ∀ x d, x ≤ N ^ d → x ≤ K * N ^ d := fun x d hx => le_trans hx (Nat.le_mul_of_pos_left _ (by omega))
  have zA : 48 + (gateCsp l + 3) * 32 + 64 ≤ Zm := by omega
  have zB : 142 ≤ Zm := by omega
  have zC : 5 + 3 + 2 + 1 + gateBetaInv l * 2 ≤ Zm := by omega
  have zD : gateCsp l + 3 ≤ Zm := by omega
  -- r, s, q
  have hr : Ledger.rowBr cr n ≤ (2 * cr + 2) * N := hNd ▸ CallIndexR.rowBr_leR cr n
  have hs : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ N ^ (gateCsp l + 3) :=
    hNd ▸ CallIndex.sp_le l n
  have hq : n ≤ N := by omega
  have hL : Ledger.Lq n ≤ N := hNd ▸ CallIndex.Lq_le_N n
  have r1 : Ledger.rowBr cr n ≤ K * N ^ 1 := by
    rw [pow_one]; exact le_trans hr (Nat.mul_le_mul_right _ hKr)
  have r48 : Ledger.rowBr cr n ^ 48 ≤ K * N ^ 48 := by
    have : Ledger.rowBr cr n ^ 48 ≤ ((2 * cr + 2) * N) ^ 48 := Nat.pow_le_pow_left hr 48
    rw [mul_pow] at this
    rw [hKd]; exact this
  have r3 : Ledger.rowBr cr n ^ 3 ≤ K * N ^ 3 := by
    have : Ledger.rowBr cr n ^ 3 ≤ ((2 * cr + 2) * N) ^ 3 := Nat.pow_le_pow_left hr 3
    rw [mul_pow] at this
    have h2 : (2 * cr + 2) ^ 3 ≤ K := by
      rw [hKd]; unfold CallIndexR.capK; exact Nat.pow_le_pow_right (by omega) (by norm_num)
    exact le_trans this (Nat.mul_le_mul_right _ h2)
  have s32 : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ^ 32 ≤ N ^ ((gateCsp l + 3) * 32) :=
    CallIndex.pw_pow hs 32
  have q64 : n ^ 64 ≤ N ^ 64 := Nat.pow_le_pow_left hq 64
  have L142 : Ledger.Lq n ^ Ledger.capExp32 .sym ≤ N ^ 142 := Nat.pow_le_pow_left hL 142
  have rs : Ledger.rowBr cr n ^ 48 * Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ^ 32 ≤
      K * N ^ (48 + (gateCsp l + 3) * 32) := by
    calc _ ≤ K * N ^ 48 * N ^ ((gateCsp l + 3) * 32) := Nat.mul_le_mul r48 s32
      _ = K * N ^ (48 + (gateCsp l + 3) * 32) := by rw [pow_add]; ring
  have rsq : Ledger.rowBr cr n ^ 48 * Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ^ 32 * n ^ 64 ≤
      K * N ^ (48 + (gateCsp l + 3) * 32 + 64) := by
    calc _ ≤ K * N ^ (48 + (gateCsp l + 3) * 32) * N ^ 64 := Nat.mul_le_mul rs q64
      _ = K * N ^ (48 + (gateCsp l + 3) * 32 + 64) := by rw [pow_add N (48 + (gateCsp l + 3) * 32) 64]; ring
  have r3q : Ledger.rowBr cr n ^ 3 * n ≤ K * N ^ 4 := by
    calc _ ≤ K * N ^ 3 * N := Nat.mul_le_mul r3 hq
      _ = K * N ^ 4 := by ring
  have hpow : Ledger.capMainPow (gateCap l) .sym (Ledger.rowBr cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n ≤
      Ledger.capMainNum (gateCap l) .sym (Ledger.rowBr cr n)
        (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n + Ledger.Lq n ^ Ledger.capExp32 .sym := by
    unfold Ledger.capMainPow
    exact le_trans (Nat.div_le_self _ _) (by omega)
  have yN : Ledger.capMainNum (gateCap l) .sym (Ledger.rowBr cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n ≤ Y := by rw [hYd]; exact hnum
  have yL : Ledger.Lq n ^ Ledger.capExp32 .sym ≤ Y := kY _ 142 zB (hNK _ _ L142)
  have yE : Ledger.capEncPow (gateCap l) (Ledger.rowBr cr n) n ≤ Y := kY _ _ zC henc
  have hCe := cEnc_le_cMain l
  exact ⟨by omega, by have := kY _ 1 (by omega) r1; omega,
    by have := kY _ _ zD (hNK _ _ hs); omega,
    by have := kY n 1 (by omega) (hNK _ _ (by rw [pow_one]; exact hq)); omega,
    by have := kY (Ledger.Lq n) 1 (by omega) (hNK _ _ (by rw [pow_one]; exact hL)); omega,
    by have := kY _ 48 (by omega) r48; omega,
    by have := kY _ _ (by omega) (hNK _ _ s32); omega,
    by have := kY _ 64 (by omega) (hNK _ _ q64); omega,
    by have := kY _ _ (by omega) rs; omega,
    by have := kY _ _ zA rsq; omega,
    by omega, by omega, by omega, by omega,
    by omega,
    by have := kY _ 3 (by omega) r3; omega,
    by have := kY _ 4 (by omega) r3q; omega,
    by omega, by omega, by omega⟩

/-! ## The SYM dimension stage's needs -/

section Need
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The SYM dimension stage's needs at the fill `W = C_v(n+1)^{D_v}`** (`NumsXS.SNeed`). -/
theorem sneed_fam (h : SB) (hZ : h.Z = CallIndexR.capZR l)
    (hZm : h.Zm = 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)
    (hCsp : h.Csp = gateCsp l) (hJ : h.J = SymSizes.schedJ l) (hcX : h.cX = SymSizes.cXg l)
    (hKL : h.KLam = SymSizes.KLam l) (hK : h.capK = CallIndexR.capK F.cr) (hcr : h.cr = F.cr)
    (hcM : h.cM = CapNum.cMain (gateCap l) .sym) {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    NumsXS.SNeed (UnaryCalc.value h.Dv h.Cv n) ((callInputs l F kclk coef A a ha).starParams n hs) (gateZeta_pos l)
      (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 h.KF F.cr := by
  obtain ⟨Wv, hWv⟩ : ∃ x, x = UnaryCalc.value h.Dv h.Cv n := ⟨_, rfl⟩
  have eW : 2 ^ (h.cW + 2 * h.Dv) * (n + 1) ^ h.Dv = Wv := by rw [hWv]; rfl
  rw [← hWv]
  obtain ⟨L, hLd⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hLn : L ≤ n + 2 := hLd ▸ clog_le_self _
  have hB : ((gate0 l F).budget kclk coef A a ha).capOf .sym n ≤ h.capK * (n + 2) ^ h.Z := by
    rw [hK, hZ]; exact sfam_capS l F kclk coef A a ha n
  have hK1 : 1 ≤ h.capK := by rw [hK]; exact CallIndexR.capK_pos _
  have hp1 : ∀ d, 1 ≤ (n + 2) ^ d := fun d => Nat.one_le_pow _ _ (by omega)
  have hpd : ∀ d d', d ≤ d' → (n + 2) ^ d ≤ (n + 2) ^ d' := fun d d' hd => Nat.pow_le_pow_right (by omega) hd
  have cK : h.capK ≤ 2 ^ Nat.clog 2 h.capK := le_two_pow_clog _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the fill
    show 2 * n + F.cr + 16 + h.KF * (n + 2) ^ 2 ≤ Wv
    have t := termY (cW := h.cW) (Dv := h.Dv) (K := h.KF + h.cr + 20) (d := 2) (n := n) (le_two_pow_clog _) (by unfold SB.cW; omega)
      (by unfold SB.Dv; omega)
    rw [eW] at t
    have p1 : n + 2 ≤ (n + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    have e : (h.KF + h.cr + 20) * (n + 2) ^ 2 = h.KF * (n + 2) ^ 2 + h.cr * (n + 2) ^ 2 + 20 * (n + 2) ^ 2 := by ring
    have c1 : h.cr ≤ h.cr * (n + 2) ^ 2 := Nat.le_mul_of_pos_right _ (hp1 2)
    rw [← hcr]; omega
  · -- the sparse bound
    have t := termY2 (cW := h.cW) (Dv := h.Dv) (a := h.sA) (b := h.sBc) (n := n) (by unfold SB.cW; omega) (by unfold SB.Dv; omega)
    rw [eW] at t
    have e1 : 3 + 32 * SymSizes.cXg l * SymSizes.schedJ l = h.sA := by unfold SB.sA; rw [hcX, hJ]
    have e2 : 6 + 32 * SymSizes.cXg l * (SymSizes.schedJ l + 1) = h.sBc := by unfold SB.sBc; rw [hcX, hJ]
    have hsp := SymSizes.sparse_le_gate l n
    rw [e1, e2] at hsp
    show SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq n)
      (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n - 1) ≤ 2 * Wv + 2
    omega
  · -- the cap's conditions
    apply capNeed_of l F.cr n (2 * Wv + 2)
    have t1 := termY (cW := h.cW) (Dv := h.Dv) (K := 2 ^ 40 * h.capK) (c := 40 + Nat.clog 2 h.capK) (d := h.Zm) (n := n)
      (by rw [pow_add]; exact Nat.mul_le_mul_left _ cK) (by unfold SB.cW; omega) (by unfold SB.Dv; omega)
    have t2 := termY (cW := h.cW) (Dv := h.Dv) (K := h.cM) (d := 0) (n := n) (le_two_pow_clog _) (by unfold SB.cW; omega) (Nat.zero_le _)
    rw [eW] at t1 t2
    rw [pow_zero, mul_one] at t2
    rw [← hK, ← hZm, ← hcM]
    have e : 2 ^ 40 * h.capK * (n + 2) ^ h.Zm = 2 ^ 40 * (h.capK * (n + 2) ^ h.Zm) := by ring
    rw [e] at t1
    omega
  · -- `Λ`
    have t := termY (cW := h.cW) (Dv := h.Dv) (K := h.KLam) (d := 3) (n := n) (le_two_pow_clog _) (by unfold SB.cW; omega) (by unfold SB.Dv; omega)
    rw [eW] at t
    have hl := SymSizes.lambda_le l n
    rw [← hKL] at hl
    show Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 n ≤ 2 * Wv + 2
    omega
  · -- the cap's square
    show (((gate0 l F).budget kclk coef A a ha).capOf .sym n * 33554432 + 2) *
        (((gate0 l F).budget kclk coef A a ha).capOf .sym n * 33554432 + 2) +
        ((gate0 l F).budget kclk coef A a ha).capOf .sym n * 33554432 + 10 ≤ 2 * Wv + 2
    obtain ⟨Bv, hBv⟩ : ∃ x, x = ((gate0 l F).budget kclk coef A a ha).capOf .sym n := ⟨_, rfl⟩
    rw [← hBv]; rw [← hBv] at hB
    obtain ⟨Y1, hY1⟩ : ∃ y, y = h.capK * (n + 2) ^ h.Z := ⟨_, rfl⟩
    rw [← hY1] at hB
    have a2 : 1 ≤ Y1 := by rw [hY1]; exact Nat.mul_le_mul hK1 (hp1 _)
    have hX : Bv * 33554432 + 2 ≤ 67108864 * Y1 := by omega
    have hXX := Nat.mul_le_mul hX hX
    have e : 67108864 * Y1 * (67108864 * Y1) = 2 ^ 52 * h.capK ^ 2 * (n + 2) ^ (2 * h.Z) := by
      rw [hY1, two_mul, pow_add]; ring
    rw [e] at hXX
    have c2 : h.capK ^ 2 ≤ 2 ^ (2 * Nat.clog 2 h.capK) := by
      calc h.capK ^ 2 ≤ (2 ^ Nat.clog 2 h.capK) ^ 2 := Nat.pow_le_pow_left cK 2
        _ = 2 ^ (2 * Nat.clog 2 h.capK) := by rw [← pow_mul, Nat.mul_comm]
    have t := termY (cW := h.cW) (Dv := h.Dv) (K := 2 ^ 52 * h.capK ^ 2) (c := 52 + 2 * Nat.clog 2 h.capK)
      (d := 2 * h.Z) (n := n) (by rw [pow_add]; exact Nat.mul_le_mul_left _ c2) (by unfold SB.cW; omega)
      (by unfold SB.Dv; omega)
    rw [eW] at t
    obtain ⟨P2, hP2⟩ : ∃ p, p = 2 ^ 52 * h.capK ^ 2 * (n + 2) ^ (2 * h.Z) := ⟨_, rfl⟩
    rw [← hP2] at t hXX
    have hX1 : Bv * 33554432 + 2 ≤ (Bv * 33554432 + 2) * (Bv * 33554432 + 2) := Nat.le_mul_self _
    omega
  · -- phase C's sum
    have hT := SymSizes.tS_le_poly (((gate0 l F).budget kclk coef A a ha).capOf .sym n) h.capK h.Z n hB
    have t1 := termY (cW := h.cW) (Dv := h.Dv) (K := h.KT) (d := h.Z + 2) (n := n) (le_two_pow_clog _) (by unfold SB.cW; omega)
      (by unfold SB.Dv; omega)
    have t2 := termY (cW := h.cW) (Dv := h.Dv) (K := 67108864 * (h.capK + 1)) (c := 27 + Nat.clog 2 h.capK)
      (d := h.Z) (n := n)
      (by have c1 : 1 ≤ 2 ^ Nat.clog 2 h.capK := Nat.one_le_two_pow
          have : 67108864 * (h.capK + 1) ≤ 134217728 * 2 ^ Nat.clog 2 h.capK := by omega
          rw [pow_add]; norm_num; exact this)
      (by unfold SB.cW; omega) (by unfold SB.Dv; omega)
    have t3 := termY (cW := h.cW) (Dv := h.Dv) (K := 1) (d := h.Csp + 3) (n := n) (c := 0) (by norm_num) (by unfold SB.cW; omega)
      (by unfold SB.Dv; omega)
    have t4 := termY (cW := h.cW) (Dv := h.Dv) (K := 2 * h.cr + 2) (d := 1) (n := n) (le_two_pow_clog _) (by unfold SB.cW; omega)
      (by unfold SB.Dv; omega)
    have t5 := termY (cW := h.cW) (Dv := h.Dv) (K := 54) (d := 1) (n := n) (c := 6) (by norm_num) (by unfold SB.cW; omega)
      (by unfold SB.Dv; omega)
    rw [eW] at t1 t2 t3 t4 t5
    have hsp : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ (n + 2) ^ (h.Csp + 3) := by
      rw [hCsp]; exact CallIndex.sp_le l n
    have hr : Ledger.rowBr F.cr n ≤ (2 * h.cr + 2) * (n + 2) := by rw [hcr]; exact CallIndexR.rowBr_leR F.cr n
    have hS : CanonicalFourfoldRowProgram.natCeilSqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n * 33554432) ≤
        ((gate0 l F).budget kclk coef A a ha).capOf .sym n * 33554432 + 1 :=
      SymSizes.natCeilSqrt_le_of (Nat.le_trans (Nat.le_succ _) (Nat.le_mul_self _))
    have hB1 : 64 * (67108864 * (((gate0 l F).budget kclk coef A a ha).capOf .sym n + 1)) ≤ Wv := by
      have a1 : ((gate0 l F).budget kclk coef A a ha).capOf .sym n + 1 ≤ (h.capK + 1) * (n + 2) ^ h.Z := by
        have e : (h.capK + 1) * (n + 2) ^ h.Z = h.capK * (n + 2) ^ h.Z + (n + 2) ^ h.Z := by ring
        have := hp1 h.Z; omega
      have a2 := Nat.mul_le_mul_left 67108864 a1
      have e2 : 67108864 * (h.capK + 1) * (n + 2) ^ h.Z = 67108864 * ((h.capK + 1) * (n + 2) ^ h.Z) := by ring
      rw [e2] at t2
      exact le_trans (Nat.mul_le_mul_left 64 a2) t2
    have hT1 : 64 * SymSizes.tSOf (((gate0 l F).budget kclk coef A a ha).capOf .sym n) 26 6 (Nat.clog 2 (n + 2)) ≤ Wv := by
      have eKT : 32 * (196608 * (Nat.clog 2 h.capK + 23 + h.Z) * (h.capK + 1) + 1) = h.KT := rfl
      rw [eKT] at hT
      exact le_trans (Nat.mul_le_mul_left 64 hT) t1
    have hs1 : 64 * Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ Wv := by
      rw [one_mul] at t3; exact le_trans (Nat.mul_le_mul_left 64 hsp) t3
    have hr1 : 64 * Ledger.rowBr F.cr n ≤ Wv := by rw [pow_one] at t4; exact le_trans (Nat.mul_le_mul_left 64 hr) t4
    have hL1 : 64 * (27 * Nat.clog 2 (n + 2) + 27) ≤ Wv := by
      rw [pow_one] at t5
      have a : 27 * Nat.clog 2 (n + 2) + 27 ≤ 54 * (n + 2) := by
        have := hLd ▸ hLn
        calc 27 * Nat.clog 2 (n + 2) + 27 ≤ 27 * (n + 2) + 27 * (n + 2) :=
              Nat.add_le_add (Nat.mul_le_mul_left _ this) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
          _ = 54 * (n + 2) := by ring
      exact le_trans (Nat.mul_le_mul_left 64 a) t5
    exact hT_of hS hT1 hB1 hs1 hr1 hL1
  · -- the dimension
    have hm := sfam_mS l F kclk coef A a ha hs h.KF
    rw [hm]
    have hk : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ Nat.clog 2 (n + 2) ^ 2 := hs.2.2.2.2
    rw [← hLd] at hk ⊢
    have hT := SymSizes.tS_le_poly (((gate0 l F).budget kclk coef A a ha).capOf .sym n) h.capK h.Z n hB
    rw [← hLd] at hT
    have eKT : 32 * (196608 * (Nat.clog 2 h.capK + 23 + h.Z) * (h.capK + 1) + 1) = h.KT := rfl
    rw [eKT] at hT
    have t := termY (cW := h.cW) (Dv := h.Dv) (K := h.KF + h.KT + 10) (d := h.Z + 2) (n := n) (le_two_pow_clog _) (by unfold SB.cW; omega)
      (by unfold SB.Dv; omega)
    rw [eW] at t
    have q1 : L ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left hLn 2
    have q2 := hpd 2 (h.Z + 2) (by omega)
    have q3 : n + 2 ≤ (n + 2) ^ (h.Z + 2) := le_trans (Nat.le_self_pow (by norm_num) _) q2
    have q4 : h.KF * L ^ 2 ≤ h.KF * (n + 2) ^ (h.Z + 2) := Nat.mul_le_mul_left _ (le_trans q1 q2)
    have e : (h.KF + h.KT + 10) * (n + 2) ^ (h.Z + 2) =
        h.KF * (n + 2) ^ (h.Z + 2) + h.KT * (n + 2) ^ (h.Z + 2) + 10 * (n + 2) ^ (h.Z + 2) := by ring
    omega

end Need

/-! ## Size helpers -/

/-! ## Atoms below `K_A·Q` -/

/-! ## The base constants' inequalities -/

namespace SB

end SB

/-! ## Small arithmetic -/

/-! ## The rows' and the units' budgets, generic -/

section Blocks
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimAsm.Emit

end Blocks

/-! ## The capacity's and the scrub's conditions, generic -/

section Blocks2
open NearCubicWires.WireExponent3_5.Filters

end Blocks2

end NearCubicWires.WireExponent3_5.PrimAsm.SymFam

end
