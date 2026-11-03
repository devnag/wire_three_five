import Proof.Wire_3_5.Primitive.Writers.SymHelpBase

/-! # PA2 (SYM leaf), part 10: the SYM writer's constants and its generic budgets

The SYM writer's constants are functions of the base constants `SB` (the producers' exponents and coefficients: the
call word's `C_w(n+1)^{D_w}`, `needW`, PA's data stage `symCc`, `symDc`, the FILTER and POP setups' needs and
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

/-- **The SYM writer's base constants.** -/
structure SB where
  Cw : ℕ
  Dw : ℕ
  Cnw : ℕ
  Dnw : ℕ
  Csy : ℕ
  Dsy : ℕ
  Cn : ℕ
  Dn : ℕ
  Cb : ℕ
  Db : ℕ
  Qn : ℕ
  Qd : ℕ
  Qb : ℕ
  Qe : ℕ
  Kf : ℕ
  Df : ℕ
  Kp : ℕ
  Dp : ℕ
  Z : ℕ
  Zm : ℕ
  Csp : ℕ
  J : ℕ
  cX : ℕ
  KLam : ℕ
  capK : ℕ
  cr : ℕ
  fe : ℕ
  cM : ℕ

namespace SB
variable (h : SB)

/-- The data width's degree and coefficient (`needW`). -/
def D2 : ℕ := h.Dnw + 1
def C2 : ℕ := h.Cnw + 1
/-- The sparse bound's exponents. -/
def sA : ℕ := 3 + 32 * h.cX * h.J
def sBc : ℕ := 6 + 32 * h.cX * (h.J + 1)
/-- The POP term's coefficient (degree `Z + 2`). -/
def KT : ℕ := 32 * (196608 * (Nat.clog 2 h.capK + 23 + h.Z) * (h.capK + 1) + 1)
/-- The fill's degree (every `SNeed` item). -/
def Dv : ℕ := h.Zm + 2 * h.Z + h.sA + h.Csp + 10
/-- The SYM filter's and the flat list's seed lengths: `≤ c + α·L`. -/
def aSb : ℕ := 6000 * (26 + h.Z + h.fe)
def cSb : ℕ := 6000 * (Nat.clog 2 (h.capK + 1) + 4)
def aFb : ℕ := 4 * h.Z + 264
def cFb : ℕ := 4 * Nat.clog 2 h.capK + 896
/-- **The dimension's quadratic coefficient**: every degree and log-coefficient of the call's sizes. -/
def KF : ℕ := 2000 + h.Dw + h.D2 + h.Zm + 32 * (h.Csp + 3) + h.Z + h.sA + h.aSb + h.aFb + 28 * h.Df * (h.fe + 1) + h.Dp
/-- The fill's coefficient (every `SNeed` item, `2^{c_W + 2D_v}`). -/
def cW : ℕ := Nat.clog 2 (h.KF + h.KT + 10) + Nat.clog 2 (h.KF + h.cr + 20) + Nat.clog 2 h.KT + Nat.clog 2 h.KLam +
  2 * Nat.clog 2 h.capK + Nat.clog 2 h.cM + Nat.clog 2 (2 * h.cr + 2) + Nat.clog 2 (h.J + 6) + h.sBc + 100
def Cv : ℕ := 2 ^ (h.cW + 2 * h.Dv)
/-- **The atoms' coefficient**: every size of the call is at most `K_A·Q`. -/
def cA : ℕ := Nat.clog 2 h.Cw + Nat.clog 2 h.C2 + Nat.clog 2 (2 * h.cr + 2) + Nat.clog 2 (h.J + 6) + Nat.clog 2 h.capK +
  Nat.clog 2 h.cM + h.cSb + h.cFb + h.sBc + 100
def KA : ℕ := 2 ^ h.cA
/-- The capacity `cap = K_cap·Q^{d_cap}` (the setups' needs). -/
def dcap : ℕ := h.Dn + h.Qd + 1
def Kcap : ℕ := 100 * h.KA + 200000 + h.Cn * (30 * h.KA) ^ h.Dn + h.Qn * (30 * h.KA) ^ h.Qd
/-- The scrub `R = K_r·Q^D`, `D` absolute. -/
def D : ℕ := h.dcap * (h.Db + h.Qe + h.Dp + 3) + h.Df + 3
def Kr : ℕ := 10 ^ 9 * (h.Kcap + 2) ^ 3 + h.Cb * (2 * h.Kcap) ^ h.Db + h.Qb * (2 * h.Kcap) ^ h.Qe +
  h.Kf * (30 * h.KA) ^ h.Df + h.Kp * (2 * h.Kcap + 30 * h.KA) ^ h.Dp * 32 ^ h.Dp + 10000 * h.KA + 10 ^ 9

end SB

/-! ## Helpers -/

theorem value_eq (D C x : ℕ) : UnaryCalc.value D C x = C * (x + 1) ^ D := rfl

theorem getD_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) (i : ℕ) : l.getD i 0 ≤ B := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _

theorem le_two_pow_clog (K : ℕ) : K ≤ 2 ^ Nat.clog 2 K := Nat.le_pow_clog (by norm_num) K

/-- A term of the fill: `64·K·(n+2)^d ≤ 2^{c_W + 2D_v}(n+1)^{D_v}`. -/
theorem termY {K c d cW Dv n : ℕ} (hK : K ≤ 2 ^ c) (hc : c + 6 ≤ cW) (hd : d ≤ Dv) :
    64 * (K * (n + 2) ^ d) ≤ 2 ^ (cW + 2 * Dv) * (n + 1) ^ Dv := by
  have h1 : (n + 2) ^ d ≤ (n + 2) ^ Dv := Nat.pow_le_pow_right (by omega) hd
  have h2 : (n + 2) ^ Dv ≤ 2 ^ Dv * (n + 1) ^ Dv := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have h3 : 64 * K ≤ 2 ^ cW := by
    have : 64 * K ≤ 2 ^ 6 * 2 ^ c := by
      have : (64 : ℕ) = 2 ^ 6 := by norm_num
      rw [this]; exact Nat.mul_le_mul_left _ hK
    rw [← pow_add] at this
    exact le_trans this (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h4 : 2 ^ Dv ≤ 2 ^ (2 * Dv) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 64 * (K * (n + 2) ^ d) = (64 * K) * (n + 2) ^ d := by ring
    _ ≤ 2 ^ cW * (2 ^ Dv * (n + 1) ^ Dv) := Nat.mul_le_mul h3 (le_trans h1 h2)
    _ ≤ 2 ^ cW * (2 ^ (2 * Dv) * (n + 1) ^ Dv) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4)
    _ = 2 ^ (cW + 2 * Dv) * (n + 1) ^ Dv := by rw [pow_add]; ring

/-- A log-term of the fill: `64·2^{aL+b} ≤ 2^{c_W + 2D_v}(n+1)^{D_v}`. -/
theorem termY2 {a b cW Dv n : ℕ} (hb : b + 6 ≤ cW) (ha : a ≤ Dv) :
    64 * 2 ^ (a * Nat.clog 2 (n + 2) + b) ≤ 2 ^ (cW + 2 * Dv) * (n + 1) ^ Dv := by
  have h1 := SymSizes.two_pow_le a b n
  have h2 : (n + 1) ^ a ≤ (n + 1) ^ Dv := Nat.pow_le_pow_right (by omega) ha
  have h3 : 64 * 2 ^ (b + 2 * a) ≤ 2 ^ (cW + 2 * Dv) := by
    have : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [this, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 64 * 2 ^ (a * Nat.clog 2 (n + 2) + b) ≤ 64 * (2 ^ (b + 2 * a) * (n + 1) ^ a) := Nat.mul_le_mul_left _ h1
    _ = (64 * 2 ^ (b + 2 * a)) * (n + 1) ^ a := by ring
    _ ≤ 2 ^ (cW + 2 * Dv) * (n + 1) ^ Dv := Nat.mul_le_mul h3 h2

theorem clog_le_self (x : ℕ) : Nat.clog 2 x ≤ x := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

/-! ## The capacity conditions of the SYM row's cap -/

/-! ## The SYM dimension stage's needs -/

/-- The phase-C sum of `SNeed.hT` from its big terms. -/
theorem hT_of {B S nb s r Lc W : ℕ} (hS : S ≤ B * 33554432 + 1)
    (hT : 64 * ((((nb + 9) * (2 * (2 * S) + 257)) * 3 + 1) * (Lc * 26 + 6)) ≤ W)
    (hB : 64 * (67108864 * (B + 1)) ≤ W) (hs : 64 * s ≤ W) (hr : 64 * r ≤ W) (hL : 64 * (27 * Lc + 27) ≤ W) :
    (((nb + 9) * (2 * (2 * S) + 257)) * 3 + 1) * (Lc * 26 + 6) + (((nb + 9) * (2 * (2 * S) + 257)) * 3 + 1) +
      (Lc * 26 + 6) + ((nb + 9) * (2 * (2 * S) + 257)) + (2 * (2 * S) + 257) + (nb + 9) + Lc * 26 + 26 + 6 +
      B * 8192 + 8192 + 33554432 + B + s + S + Lc + r ≤ 2 * W + 2 := by
  obtain ⟨A, hA⟩ : ∃ x, x = (nb + 9) * (2 * (2 * S) + 257) := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ x, x = (A * 3 + 1) * (Lc * 26 + 6) := ⟨_, rfl⟩
  rw [← hA, ← hTd]
  rw [← hA, ← hTd] at hT
  have t1 : A * 3 + 1 ≤ T := by rw [hTd]; exact Nat.le_mul_of_pos_right _ (by omega)
  have t2 : Lc * 26 + 6 ≤ T := by rw [hTd]; exact Nat.le_mul_of_pos_left _ (by omega)
  have t3 : 2 * (2 * S) + 257 ≤ A := by rw [hA]; exact Nat.le_mul_of_pos_left _ (by omega)
  have t4 : nb + 9 ≤ A := by rw [hA]; exact Nat.le_mul_of_pos_right _ (by omega)
  omega

section Need

end Need

/-! ## Size helpers -/

theorem stV_le {y0 y1 y2 y3 B : ℕ} (h0 : y0 + 1 ≤ B) (h1 : y1 + 1 ≤ B) (h2 : y2 + 1 ≤ B) (h3 : y3 + 1 ≤ B) :
    SymDec.stV y0 y1 y2 y3 ≤ B ^ 8 := by
  unfold SymDec.stV
  have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul (le_refl 1) h0) h0) h1) h1) h2) h2) h3) h3
  exact le_of_le_of_eq this (by ring)

/-- A product of five factors in the atoms' shape. -/
theorem prod5 {X1 X2 X3 X4 X5 c1 c2 c5 a1 a2 d3 d5 L k T n : ℕ}
    (h1 : X1 ≤ 2 ^ c1 * 2 ^ (a1 * L)) (h2 : X2 ≤ 2 ^ c2 * 2 ^ (a2 * L)) (h3 : X3 ≤ (n + 2) ^ d3)
    (h4 : X4 ≤ 2 ^ k) (h5 : X5 ≤ 2 ^ c5 * (n + 2) ^ d5) :
    X1 * X2 * X3 * X4 * X5 ≤ 2 ^ (c1 + c2 + c5) * ((n + 2) ^ (d3 + d5) * 2 ^ ((a1 + a2) * L) * 2 ^ k * 2 ^ T) := by
  have hT : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  calc X1 * X2 * X3 * X4 * X5 ≤ (2 ^ c1 * 2 ^ (a1 * L)) * (2 ^ c2 * 2 ^ (a2 * L)) * (n + 2) ^ d3 * 2 ^ k *
        (2 ^ c5 * (n + 2) ^ d5) := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4) h5
    _ = 2 ^ (c1 + c2 + c5) * ((n + 2) ^ (d3 + d5) * 2 ^ ((a1 + a2) * L) * 2 ^ k * 1) := by
        rw [pow_add, pow_add, pow_add, add_mul, pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hT)

/-- The flat list's seed length at the family: `fbv ≤ a_{Fb}·L + c_{Fb}`. -/
theorem fbv_fam (h : SB) {M B n : ℕ} (hM : M ≤ 4 * (n + 1) ^ 26) (hB : B ≤ 8192 * (h.capK * (n + 2) ^ h.Z)) :
    FlatNums.fbv M B (Nat.clog 2 (n + 2) + 5) ≤ h.aFb * Nat.clog 2 (n + 2) + h.cFb := by
  obtain ⟨L, hL⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hL]
  have hn : n + 2 ≤ 2 ^ L := by rw [hL]; exact Nat.le_pow_clog (by norm_num) _
  have hB' : B ≤ 2 ^ ((13 + Nat.clog 2 h.capK) + h.Z * L) := by
    have a1 : (n + 2) ^ h.Z ≤ 2 ^ (h.Z * L) := by
      rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left hn _
    have a2 : h.capK ≤ 2 ^ Nat.clog 2 h.capK := le_two_pow_clog _
    calc B ≤ 8192 * (h.capK * (n + 2) ^ h.Z) := hB
      _ ≤ 8192 * (2 ^ Nat.clog 2 h.capK * 2 ^ (h.Z * L)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul a2 a1)
      _ = 2 ^ ((13 + Nat.clog 2 h.capK) + h.Z * L) := by rw [pow_add, pow_add]; norm_num; ring
  have hM' : M ≤ 2 ^ (2 + 26 * L) := by
    have a1 : (n + 1) ^ 26 ≤ 2 ^ (26 * L) := by
      rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left (by omega) _
    calc M ≤ 4 * (n + 1) ^ 26 := hM
      _ ≤ 4 * 2 ^ (26 * L) := Nat.mul_le_mul_left _ a1
      _ = 2 ^ (2 + 26 * L) := by rw [pow_add]; norm_num
  have := fbv_le M B L (13 + Nat.clog 2 h.capK) 2 h.Z 26 hB' hM'
  unfold SB.aFb SB.cFb
  exact le_of_le_of_eq this (by ring)

/-- The FILTER row's error factor at the family: `(L_s+2)^{D_f(fe·L+1)} ≤ 2^{K_F L²}`. -/
theorem exp_filter {Ls fe Df KF n : ℕ} (hLs : Ls ≤ 2 * (n + 1) ^ 26) (hK : 28 * Df * (fe + 1) ≤ KF) :
    (Ls + 2) ^ (Df * (fe * Nat.clog 2 (n + 2) + 1)) ≤ 2 ^ (KF * Nat.clog 2 (n + 2) ^ 2) := by
  obtain ⟨L, hL⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hL]
  have hn : n + 2 ≤ 2 ^ L := by rw [hL]; exact Nat.le_pow_clog (by norm_num) _
  have hL1 : 1 ≤ L := by rw [hL]; exact Nat.clog_pos (by norm_num) (by omega)
  have a1 : (n + 1) ^ 26 ≤ 2 ^ (26 * L) := by
    rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left (by omega) _
  have a2 : Ls + 2 ≤ 2 ^ (26 * L + 2) := by
    rw [pow_add]; have : 1 ≤ 2 ^ (26 * L) := Nat.one_le_two_pow; omega
  have b1 : fe * L + 1 ≤ (fe + 1) * L := by rw [add_mul, one_mul]; omega
  have b2 : 26 * L + 2 ≤ 28 * L := by omega
  have a3 : (fe * L + 1) * (26 * L + 2) ≤ 28 * (fe + 1) * L ^ 2 :=
    le_of_le_of_eq (Nat.mul_le_mul b1 b2) (by ring)
  have a4 : Df * ((fe * L + 1) * (26 * L + 2)) ≤ KF * L ^ 2 := by
    calc Df * ((fe * L + 1) * (26 * L + 2)) ≤ Df * (28 * (fe + 1) * L ^ 2) := Nat.mul_le_mul_left _ a3
      _ = 28 * Df * (fe + 1) * L ^ 2 := by ring
      _ ≤ KF * L ^ 2 := Nat.mul_le_mul_right _ hK
  calc (Ls + 2) ^ (Df * (fe * L + 1)) ≤ (2 ^ (26 * L + 2)) ^ (Df * (fe * L + 1)) := Nat.pow_le_pow_left a2 _
    _ = 2 ^ (Df * ((fe * L + 1) * (26 * L + 2))) := by rw [← pow_mul]; congr 1; ring
    _ ≤ 2 ^ (KF * L ^ 2) := Nat.pow_le_pow_right (by norm_num) a4

/-- The POP row's counting capacity at the family: `(8L_p+2)^{3·lbP+1} ≤ 2^T`. -/
theorem popY_fam {Pl : Lists.FlatListParams} {BS Lp n : ℕ} (hB : Pl.B ≤ BS * 8192) (hLp : Lp ≤ (n + 1) ^ 26) :
    (8 * Lp + 2) ^ (3 * PopLink.lbP Pl + 1) ≤ 2 ^ SymSizes.tSOf BS 26 6 (Nat.clog 2 (n + 2)) := by
  obtain ⟨L, hL⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hL]
  have hn : n + 2 ≤ 2 ^ L := by rw [hL]; exact Nat.le_pow_clog (by norm_num) _
  have a1 : (n + 1) ^ 26 ≤ 2 ^ (26 * L) := by
    rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left (by omega) _
  have hc : Nat.clog 2 (8 * Lp + 2) ≤ L * 26 + 6 := by
    apply Nat.clog_le_of_le_pow
    have : 1 ≤ 2 ^ (26 * L) := Nat.one_le_two_pow
    have e : 2 ^ (L * 26 + 6) = 64 * 2 ^ (26 * L) := by rw [pow_add, Nat.mul_comm L 26]; ring
    rw [e]; omega
  have := SymSizes.popY_le Pl (BS * 8192) Lp (L * 26 + 6) hB hc
  have e : 64 ^ 2 * (BS * 8192) = BS * 33554432 := by ring
  rw [e] at this
  exact this

/-! ## Atoms below `K_A·Q` -/

/-- An atom `X ≤ 2^c·(n+2)^d·2^{aL}·2^k·2^T` with `c ≤ c_A`, `d + a ≤ K_F` is at most `K_A·Q`. -/
theorem atomQ {X c d a k T KF cA n : ℕ} (hX : X ≤ 2 ^ c * ((n + 2) ^ d * 2 ^ (a * Nat.clog 2 (n + 2)) * 2 ^ k * 2 ^ T))
    (hc : c ≤ cA) (hda : d + a ≤ KF) :
    X ≤ 2 ^ cA * (2 ^ (k + Nat.clog 2 (n + 2) + KF * Nat.clog 2 (n + 2) ^ 2 + T) + 1) := by
  have h1 := toQ n d a k T KF hda
  have h2 : 2 ^ c ≤ 2 ^ cA := Nat.pow_le_pow_right (by norm_num) hc
  calc X ≤ 2 ^ c * ((n + 2) ^ d * 2 ^ (a * Nat.clog 2 (n + 2)) * 2 ^ k * 2 ^ T) := hX
    _ ≤ 2 ^ cA * 2 ^ (k + Nat.clog 2 (n + 2) + KF * Nat.clog 2 (n + 2) ^ 2 + T) := Nat.mul_le_mul h2 h1
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)


/-- An atom's shape with the free factors `2^k·2^T`. -/
theorem atomE2 {X c d a L k T N : ℕ} (hX : X ≤ 2 ^ c * (N ^ d * 2 ^ (a * L))) :
    X ≤ 2 ^ c * (N ^ d * 2 ^ (a * L) * 2 ^ k * 2 ^ T) :=
  le_trans hX (Nat.mul_le_mul_left _ (le_trans (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)
    (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)))

/-! ## The base constants' inequalities -/

namespace SB
variable (h : SB)

theorem cA_ge : Nat.clog 2 h.Cw ≤ h.cA ∧ Nat.clog 2 h.C2 ≤ h.cA ∧ 13 + Nat.clog 2 h.capK ≤ h.cA ∧
    h.cSb + 1 ≤ h.cA ∧ h.cFb + 1 ≤ h.cA ∧ h.cSb + h.cFb + 7 ≤ h.cA ∧ 4 + Nat.clog 2 (2 * h.cr + 2) ≤ h.cA ∧
    h.sBc ≤ h.cA ∧ 1 + Nat.clog 2 (h.J + 6) ≤ h.cA ∧ 40 + Nat.clog 2 h.capK ≤ h.cA ∧ Nat.clog 2 h.cM ≤ h.cA ∧
    1 ≤ h.cA ∧ 3 ≤ h.cA ∧ 6 ≤ h.cA ∧ 7 ≤ h.cA := by
  unfold SB.cA; omega

theorem KF_ge : h.Dw ≤ h.KF ∧ h.D2 ≤ h.KF ∧ 26 ≤ h.KF ∧ 1 ≤ h.KF ∧ h.Z ≤ h.KF ∧ 0 + h.aSb ≤ h.KF ∧
    0 + h.aFb ≤ h.KF ∧ 208 + 26 + (h.aSb + h.aFb) ≤ h.KF ∧ 0 + h.fe ≤ h.KF ∧ 1 + (h.fe + 4) ≤ h.KF ∧
    0 + h.sA ≤ h.KF ∧ h.Csp + 3 ≤ h.KF ∧ h.Zm ≤ h.KF ∧ 208 ≤ h.KF ∧ 26 + 0 ≤ h.KF ∧
    28 * h.Df * (h.fe + 1) ≤ h.KF ∧ h.Dp ≤ h.KF := by
  unfold SB.KF SB.aSb; omega

theorem cap_ge : 1 ≤ h.dcap ∧ h.Dn ≤ h.dcap ∧ h.Qd ≤ h.dcap ∧ 100 * h.KA + 200000 ≤ h.Kcap ∧
    h.Cn * (30 * h.KA) ^ h.Dn ≤ h.Kcap ∧ h.Qn * (30 * h.KA) ^ h.Qd ≤ h.Kcap := by
  unfold SB.dcap SB.Kcap; omega

theorem D_ge : 3 * h.dcap ≤ h.D ∧ h.dcap * h.Db ≤ h.D ∧ h.dcap * h.Qe ≤ h.D ∧ h.dcap * h.Dp + 1 ≤ h.D ∧
    h.Df + 1 ≤ h.D ∧ 1 ≤ h.D := by
  unfold SB.D
  have e : h.dcap * (h.Db + h.Qe + h.Dp + 3) = h.dcap * h.Db + h.dcap * h.Qe + h.dcap * h.Dp + 3 * h.dcap := by ring
  omega

theorem data_ge : h.Cnw ≤ h.C2 ∧ h.Dnw ≤ h.D2 := by unfold SB.C2 SB.D2; omega

end SB

/-! ## Small arithmetic -/

theorem n3_le (n : ℕ) : n + 3 ≤ 2 * (n + 2) := by omega

theorem lin16 {x y : ℕ} (h : 2 * x + 2 ≤ y) : 2 * x + 20 ≤ 2 ^ 4 * y := by omega

theorem t5_le {t J L n c : ℕ} (hr : t ≤ J * (L + 1) + 1) (hL : L ≤ n + 2) (hc : J + 6 ≤ 2 ^ c) :
    t + 5 ≤ 2 ^ (1 + c) * (n + 2) ^ 1 := by
  have q1 : J * (L + 1) ≤ J * (n + 3) := Nat.mul_le_mul_left _ (by omega)
  have q2 : J * (n + 3) = J * (n + 2) + J := by ring
  have q3 : (J + 6) * (n + 2) ≤ 2 ^ c * (n + 2) := Nat.mul_le_mul_right _ hc
  have q4 : (J + 6) * (n + 2) = J * (n + 2) + 6 * (n + 2) := by ring
  have q5 : J ≤ J * (n + 2) := Nat.le_mul_of_pos_right _ (by omega)
  rw [pow_one, pow_add, pow_one, Nat.mul_assoc]
  omega

/-- The units per state `EU = R(M+3)+2`, `R = |carriers| + 2a`, at most `2^7(n+2)^{26}`. -/
theorem euV_le {M nc a X Y : ℕ} (hM : M ≤ 4 * X) (hnc : nc ≤ 2) (ha : a ≤ 4) (hXY : X ≤ Y) (hY : 1 ≤ Y) :
    SymDec.euV M nc a ≤ 2 ^ 7 * Y := by
  unfold SymDec.euV
  have q1 : (M + 3) * (nc + a + a) ≤ (4 * Y + 3) * 10 := Nat.mul_le_mul (by omega) (by omega)
  norm_num; omega

theorem mix_le {M nc a X Y : ℕ} (hM : M ≤ 4 * X) (hnc : nc ≤ 2) (ha : a ≤ 4) (hXY : X ≤ Y) (hY : 1 ≤ Y) :
    (nc + 2 * a) * (M + 3) + 2 ≤ 2 ^ 7 * Y := by
  have q1 : (nc + 2 * a) * (M + 3) ≤ 10 * (4 * Y + 3) := Nat.mul_le_mul (by omega) (by omega)
  norm_num; omega

/-! ## The rows' and the units' budgets, generic -/

section Blocks
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- **The FILTER rows' needs and pipeline bounds** (`sym_ready`'s `hFN`), from the rows' sizes. -/
theorem fn_block {W : PrimT.WalkBank.WalkBankProducer} (FS : FiltSetup.FiltSetupSpec5 W) (h : SB)
    (hFS1 : FS.Cn = h.Cn) (hFS2 : FS.Dn = h.Dn)
    (hfp : ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
      FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
        h.Kf * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ h.Df * (L + 2) ^ (h.Df * (P.errExp + 1)))
    (P : GapParams) {n x0 x1 ys sb k kh BS E Qv KQ cap BPf BPp nc : ℕ}
    (hPl : P.len = 2 * (n + 1) ^ 26) (hPc : P.cap = BS) (hPe : P.errExp = E)
    (hcard : Fintype.card (GapSeed P) = 2 ^ sb) (hBS1 : 1 ≤ BS)
    (hx0 : x0 ≤ (n + 1) ^ 26) (hx1 : x1 ≤ (n + 1) ^ 26) (hys : ys ≤ 4 * (n + 1) ^ 26) (h2k : 2 * kh = k)
    (a26 : 8 * (n + 1) ^ 26 ≤ KQ) (aBS : 8192 * BS ≤ KQ) (aerr : E ≤ KQ) (akk : 8 * 2 ^ k ≤ KQ)
    (asb : 2 * 2 ^ sb ≤ KQ) (hcapN : h.Cn * (30 * KQ) ^ h.Dn ≤ cap)
    (hexp : ∀ Ls, Ls ≤ 2 * (n + 1) ^ 26 → (Ls + 2) ^ (h.Df * (E + 1)) ≤ Qv)
    (hBPf : BPf = h.Kf * (30 * KQ) ^ h.Df * Qv) :
    ∀ (eg : GapSeed P) (r row : ℕ), r < nc → row < 2 ^ (2 * kh) →
      FS.need P.len P.cap P.errExp (fbL r x0 x1) (2 * (2 * row)) (2 * (x0 + x1) + ys) (fbOff r x0)
          (Fintype.card (GapSeed P)) ≤ cap ∧
      FiltPipe.filtPipeBound P eg (fbL r x0 x1) (2 * (2 * row)) (2 * (x0 + x1) + ys) (fbOff r x0)
          (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤ BPf + BPp := by
  intro eg r row hr hrow
  rw [h2k] at hrow
  have hfL : fbL r x0 x1 ≤ 2 * (n + 1) ^ 26 := by unfold fbL; split_ifs <;> omega
  have hfO : fbOff r x0 ≤ 2 * (n + 1) ^ 26 := by unfold fbOff; split_ifs <;> omega
  refine ⟨?_, ?_⟩
  · have hp := FS.need_poly P.len P.cap P.errExp (fbL r x0 x1) (2 * (2 * row)) (2 * (x0 + x1) + ys) (fbOff r x0)
      (Fintype.card (GapSeed P))
    unfold ValidatorPolynomialDomination.PolyBounded at hp
    rw [hFS1, hFS2] at hp
    refine le_trans hp (le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)) hcapN)
    rw [hPl, hPc, hPe, hcard]
    omega
  · have hb := hfp P eg (fbL r x0 x1) (2 * (2 * row)) (2 * (x0 + x1) + ys) (fbOff r x0) (by rw [hPc]; exact hBS1)
    refine le_trans hb ?_
    rw [hPl, hPc, hPe]
    calc _ ≤ h.Kf * (30 * KQ) ^ h.Df * Qv :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) (hexp _ hfL)
      _ = BPf := hBPf.symm
      _ ≤ BPf + BPp := Nat.le_add_right _ _

/-- **The unit's budget** (`sym_ready`'s `hnU`): at most `R − 1`. -/
theorem nu_block (h : SB) {n a nc V X ys ul cr fe t sp Lq cap Bb FSb Qbd BPf BPp b R KQ Y : ℕ}
    (hn : n + 2 ≤ cap) (ha : a ≤ 4) (hnc : nc ≤ 2) (hV : V ≤ cap) (hX : X ≤ cap) (hys : ys ≤ cap)
    (hcr : cr ≤ cap) (hfe : fe ≤ cap) (ht : t ≤ cap) (hsp : sp ≤ cap) (hLq : Lq ≤ cap)
    (hBb : Bb = SymDec.fbCost cap + FSb + (SymDec.pbCost cap + Qbd))
    (hul : ul ≤ KQ) (hb : b = KQ) (hR : R = h.Kr * Y) (hKQ : KQ ≤ h.KA * Y)
    (fc3 : (cap + 2) * (cap + 2) * (cap + 2) ≤ (h.Kcap + 2) ^ 3 * Y)
    (fCb : FSb ≤ h.Cb * (2 * h.Kcap) ^ h.Db * Y) (fQb : Qbd ≤ h.Qb * (2 * h.Kcap) ^ h.Qe * Y)
    (fBPf : BPf ≤ h.Kf * (30 * h.KA) ^ h.Df * Y)
    (fBPp : BPp ≤ h.Kp * (2 * h.Kcap + 30 * h.KA) ^ h.Dp * 32 ^ h.Dp * Y) (hY1 : 1 ≤ Y) :
    SymDec.symNU ul (4 * UnaryPow.sq cap + 1 + (SymDec.reqParseCost n a nc V + 1 + (5 * UnaryPow.sq cap + 1 +
        (30 * UnaryPow.sq cap + 1 + SymDec.countsCost nc X ys))) + 1 +
        (SymDec.starCapCost n cr fe t sp Lq cap + 1 + (500 * UnaryPow.sq cap + 1 + (30 * UnaryPow.sq cap + 1 +
          26 * UnaryPow.sq cap))) + 1 + (Bb + 12)) (BPf + BPp) b ≤ R - 1 := by
  unfold SymDec.symNU
  rw [HashSizes.cpCost_eq, hb, hR]
  have c23 : (cap + 2) * (cap + 2) ≤ (cap + 2) * (cap + 2) * (cap + 2) := Nat.le_mul_of_pos_right _ (by omega)
  have c13 : cap + 2 ≤ (cap + 2) * (cap + 2) := Nat.le_mul_of_pos_right _ (by omega)
  have hsq : UnaryPow.sq cap = 200 * ((cap + 2) * (cap + 2)) := by unfold UnaryPow.sq; ring
  have r1 := SymSizes.reqParseCost_le n a nc V cap (by omega) ha (by omega) hV
  have r2 := SymSizes.countsCost_le nc X ys cap (by omega) hX hys
  have r3 := SymSizes.starCapCost_le n cr fe t sp Lq cap hn hcr hfe ht hsp hLq
  have r4 := SymSizes.fbCost_le cap
  have r5 := SymSizes.pbCost_eq cap
  have eKr : h.Kr * Y = 1000000000 * ((h.Kcap + 2) ^ 3 * Y) + h.Cb * (2 * h.Kcap) ^ h.Db * Y +
      h.Qb * (2 * h.Kcap) ^ h.Qe * Y + h.Kf * (30 * h.KA) ^ h.Df * Y +
      h.Kp * (2 * h.Kcap + 30 * h.KA) ^ h.Dp * 32 ^ h.Dp * Y + 10000 * (h.KA * Y) + 1000000000 * Y := by
    unfold SB.Kr; ring
  rw [hsq]
  omega

end Blocks

/-! ## The capacity's and the scrub's conditions, generic -/

section Blocks2
open NearCubicWires.WireExponent3_5.Filters

theorem L7 {n X : ℕ} (h : n + 1 ≤ X) : n + 2 + 5 ≤ 8 * X := by omega

theorem r4_le {row K : ℕ} (h : row < K) : 2 * (2 * row) + 4 ≤ 8 * K := by omega

theorem ul_le {X : ℕ} (h : 3 ≤ X) : (2 + 4) * (X + 1) ≤ 8 * X := by omega

/-- **The decode's numbers stage needs** (`sym_ready`'s `hN2`). -/
theorem nn_block {n BS err ys nc Lq kh a y0 y1 y2 y3 KQ cap k : ℕ}
    (hBS1 : 1 ≤ BS) (hcapKQ : 100 * KQ + 200000 ≤ cap) (aBS : 8192 * BS ≤ KQ) (a26 : 8 * (n + 1) ^ 26 ≤ KQ)
    (herr : err ≤ KQ) (asb : 2 * 2 ^ (SymDec.gP n BS err).seedBits ≤ KQ) (hLq : Lq ≤ n + 2) (hn : n + 2 ≤ KQ)
    (hbV : SymDec.bV nc BS ≤ 8192 * BS) (hys : ys ≤ 4 * (n + 1) ^ 26)
    (afb : 2 * 2 ^ FlatNums.fbv ys (SymDec.bV nc BS) (Lq + 5) ≤ KQ)
    (h2k : 2 * kh = k) (akk : 8 * 2 ^ k ≤ KQ) (atot : SymDec.totV n BS err ys nc Lq kh a y0 y1 y2 y3 ≤ KQ)
    (hnc : nc ≤ 2) (ha : a ≤ 4) (hy4 : y0 + y1 + y2 + y3 = ys) :
    SymDec.NumsNeed cap n BS err ys nc Lq kh a y0 y1 y2 y3 := by
  have g1 : (SymDec.gP n BS err).cap = BS := rfl
  have g2 : (SymDec.gP n BS err).len = 2 * (n + 1) ^ 26 := rfl
  have g3 : (SymDec.gP n BS err).errExp = err := rfl
  have l1 := clog_le_self (32 * (SymDec.gP n BS err).cap)
  have l2 := clog_le_self (SymDec.gP n BS err).len
  have l3 : (SymDec.gP n BS err).labelBits ≤ 32 * (SymDec.gP n BS err).cap + (SymDec.gP n BS err).len := by
    unfold GapParams.labelBits GapParams.prefixBits
    exact max_le (le_trans l1 (Nat.le_add_right _ _)) (le_trans l2 (Nat.le_add_left _ _))
  have l4 : (SymDec.gP n BS err).fieldBits ≤ (SymDec.gP n BS err).len + 4 := by
    unfold GapParams.fieldBits; exact Nat.add_le_add_right l2 4
  have l5 : (SymDec.gP n BS err).walkLen ≤ (SymDec.gP n BS err).errExp + 1 := by
    unfold GapParams.walkLen; omega
  refine ⟨hBS1, by omega, by omega, by omega, ?_, by omega, by omega, ?_, ?_, by omega, by omega⟩
  · rw [pow_succ]; omega
  · rw [pow_succ]; omega
  · rw [h2k, pow_succ]; omega

/-- **The capacity's call-size conditions** (`sym_ready`'s `hI`, `hcF`, `hcB`, `hcS`, `hcP` and the cap's bound). -/
theorem cap_block {n nc KQ cap b tot eu ys st fb2 kh k x0 x1 bv Lq fe cr sp X : ℕ}
    (hcapKQ : 100 * KQ + 200000 ≤ cap) (hb : b = KQ) (atot : tot ≤ KQ) (aeu : eu ≤ KQ)
    (hys : ys ≤ 4 * (n + 1) ^ 26) (a26 : 8 * (n + 1) ^ 26 ≤ KQ) (h2k : 2 * kh = k) (akk : 8 * 2 ^ k ≤ KQ)
    (ast : st ≤ KQ) (afb : 2 * fb2 ≤ KQ) (hnc : nc ≤ 2) (hx0 : x0 ≤ (n + 1) ^ 26) (hx1 : x1 ≤ (n + 1) ^ 26)
    (hbv : bv ≤ KQ) (hLq : Lq ≤ n + 2) (hn : n + 2 ≤ KQ) (afe4 : (fe + 4) * (n + 3) ≤ KQ)
    (acr : 2 * cr + 20 ≤ KQ) (asp : sp ≤ KQ) (aX : X ≤ 2 * KQ) :
    b + tot + eu + 2 * ys + 2 ^ (2 * kh) + st + fb2 + nc + 20 ≤ cap ∧
    4 * 2 ^ (2 * kh) + 2 * (x0 + x1) + ys ≤ cap ∧
    st + 7 * ys + bv + Lq + fb2 + 4 * 2 ^ (2 * kh) + 2 * (x0 + x1) + 40 ≤ cap ∧
    (fe + 4) * (n + 3) + 2 * cr + 20 ≤ cap ∧ sp ≤ cap ∧ X ≤ cap := by
  rw [h2k]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The request's first stage needs** (`sym_ready`'s `hN1`). -/
theorem p1_block {n a nc cap KQ V X : ℕ} (w : List Bool) (codes ccs cx cy : List ℕ) (hcodes : codes.length = a)
    (hccs : ccs.length = nc) (hcxl : cx.length = nc) (hwl : w.length ≤ KQ) (ha : a ≤ 4) (hnc : nc ≤ 2)
    (hV : V ≤ KQ) (hn : n + 2 ≤ KQ) (hxs : cx.sum ≤ 2 * X) (hys : cy.sum ≤ 4 * X) (a26 : 8 * X ≤ KQ)
    (hcapKQ : 100 * KQ + 200000 ≤ cap) : SymDec.P1Need cap w n codes ccs cx cy V X := by
  have b1 : 2 ^ (natBitLength n + 1) ≤ 4 * n + 4 := by
    have := CopyNat.two_pow_natBitLength_le n; rw [pow_succ]; omega
  have b2 := PrimT.C4GateSym.nbl_small a ha
  have b3 := PrimT.C4GateSym.nbl_small nc (by omega)
  refine ⟨by omega, ?_, by omega, by omega⟩
  rw [hcodes, hccs]; omega

/-- **The scrub's conditions** (`sym_ready`'s `hcap`, `hR` and the boot's bound). -/
theorem r_block (h : SB) {cap R Y KQ wl n : ℕ} (hR : R = h.Kr * Y)
    (fc3 : (cap + 2) * (cap + 2) * (cap + 2) ≤ (h.Kcap + 2) ^ 3 * Y) (hKQ : KQ ≤ h.KA * Y) (hwl : wl ≤ KQ)
    (hn : n + 2 ≤ KQ) (hY1 : 1 ≤ Y) :
    cap + 1 ≤ R ∧ R - 1 + 1 ≤ R ∧ 4 * wl + 100 * (n + 2) ≤ R := by
  have c3 : cap + 2 ≤ (cap + 2) * (cap + 2) * (cap + 2) :=
    le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have eKr : h.Kr * Y = 1000000000 * ((h.Kcap + 2) ^ 3 * Y) + h.Cb * (2 * h.Kcap) ^ h.Db * Y +
      h.Qb * (2 * h.Kcap) ^ h.Qe * Y + h.Kf * (30 * h.KA) ^ h.Df * Y +
      h.Kp * (2 * h.Kcap + 30 * h.KA) ^ h.Dp * 32 ^ h.Dp * Y + 10000 * (h.KA * Y) + 1000000000 * Y := by
    unfold SB.Kr; ring
  rw [hR, eKr]
  exact ⟨by omega, by omega, by omega⟩

end Blocks2

end NearCubicWires.WireExponent3_5.PrimAsm.SymFam
