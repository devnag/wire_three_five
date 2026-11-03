import Proof.Wire_3_5.Primitive.Writers.SBCostBase

/-! # SB: the capacity target, part 1 — P1's phase sums within one majorant

* `clog_le`, `nbl_le`, **`atoms`** (the star numbers within `n`, `n²`; `clog`, `natBitLength` within their arguments);
* `tB1_le` … `tC3_le`: each phase sum within `10^6·Z`, `Z = (n+1)^26 + B_m(n) + fe·(2n+4) + n² + c0 + c1 + nc + 10`.

Paper quantity of the main types: SB's capacity (`prim:runtime`, P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

theorem clog_le (x : ℕ) : Nat.clog 2 x ≤ x := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

theorem nbl_le (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength; have := Nat.log_le_self 2 x; omega

/-- The atoms of the phase sums. -/
theorem atoms (P : Shared.StarParams) (fe CAP : ℕ) :
    P.r ≤ P.n ∧ P.s ≤ P.n ∧ P.b ≤ P.n ∧ P.r * P.b ≤ P.n ∧ P.k ≤ P.n * P.n ∧ P.s * (P.r / 2) ≤ P.n * P.n ∧
    (P.b - P.s) * (P.r / 2) ≤ P.n ∧ fe * Nat.clog 2 (P.n + 2) ≤ fe * (2 * P.n + 4) ∧ P.n + 1 ≤ (P.n + 1) ^ 26 ∧
    natBitLength ((P.n + 1) ^ 26 * 2 - 1) ≤ (P.n + 1) ^ 26 * 2 ∧ natBitLength (CAP * 32 - 1) ≤ CAP * 32 + 1 ∧
    Nat.clog 2 (P.n + 2) ≤ P.n + 2 := by
  have hr : P.r ≤ P.n := by have := P.four_r_le_n; omega
  have hr2 : 2 ≤ P.r := P.two_le_r
  have hrb := P.r_mul_b_le
  have hb : P.b ≤ P.n := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hrb
  have hsb : P.s ≤ P.b := by have e := P.b_succ; have := @Nat.lt_two_pow_self P.s; omega
  have hs : P.s ≤ P.n := hsb.trans hb
  have hcl := clog_le (P.n + 2)
  have hY : P.n + 1 ≤ (P.n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  have h1 := nbl_le ((P.n + 1) ^ 26 * 2 - 1)
  have h2 := nbl_le (CAP * 32 - 1)
  have hY1 : 1 ≤ (P.n + 1) ^ 26 := Nat.one_le_pow _ _ (by omega)
  refine ⟨hr, hs, hb, hrb, Nat.mul_le_mul hr hs, Nat.mul_le_mul hs (le_trans (Nat.div_le_self _ _) hr), ?_,
    Nat.mul_le_mul_left _ (by omega), hY, by omega, by omega, hcl⟩
  calc (P.b - P.s) * (P.r / 2) ≤ P.b * P.r := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.div_le_self _ _)
    _ = P.r * P.b := Nat.mul_comm _ _
    _ ≤ P.n := hrb

theorem tB1_le (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe mb nc c0 c1 : ℕ) (hmb : mb ≤ 1) :
    tB1 P h0 h1 Cδ C m fe mb nc c0 c1 ≤ 10 ^ 6 * ((P.n + 1) ^ 26 + Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + fe * (2 * P.n + 4) + P.n * P.n + c0 + c1 + nc + 10) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := atoms P fe (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
  unfold tB1
  generalize (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) = CAP at a11 ⊢
  generalize (P.n + 1) ^ 26 = Y at a9 a10 ⊢
  generalize natBitLength (CAP * 32 - 1) = NB2 at a11 ⊢
  generalize natBitLength (Y * 2 - 1) = NB1 at a10 ⊢
  have hmx : max NB2 NB1 ≤ CAP * 32 + Y * 2 + 1 := by clear * - a10 a11; omega
  generalize max NB2 NB1 = MX at hmx ⊢
  generalize Nat.clog 2 (P.n + 2) = L at a8 a12 ⊢
  generalize fe * L = FL at a8 ⊢
  have hx : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  generalize P.n - P.r * P.b = XX at hx ⊢
  have d1 : (XX + 1) / 2 ≤ XX + 1 := Nat.div_le_self _ _
  have d2 : XX / 2 ≤ XX := Nat.div_le_self _ _
  have d3 : (XX + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d4 : XX % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d5 : FL / 4 ≤ FL := Nat.div_le_self _ _
  have d6 : FL % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have d7 : P.r / 2 ≤ P.r := Nat.div_le_self _ _
  generalize (XX + 1) / 2 = D1 at d1 ⊢
  generalize XX / 2 = D2 at d2 ⊢
  generalize (XX + 1) % 2 = D3 at d3 ⊢
  generalize XX % 2 = D4 at d4 ⊢
  generalize FL / 4 = D5 at d5 ⊢
  generalize FL % 4 = D6 at d6 ⊢
  generalize P.r / 2 = D7 at d7 a6 a7 ⊢
  clear * - a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hmb hmx hx d1 d2 d3 d4 d5 d6 d7
  omega

theorem tB2a_le (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe mb nc c0 c1 : ℕ) (hmb : mb ≤ 1) :
    tB2a P h0 h1 Cδ C m fe mb nc c0 c1 ≤ 10 ^ 6 * ((P.n + 1) ^ 26 + Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + fe * (2 * P.n + 4) + P.n * P.n + c0 + c1 + nc + 10) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := atoms P fe (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
  unfold tB2a
  generalize (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) = CAP at a11 ⊢
  generalize (P.n + 1) ^ 26 = Y at a9 a10 ⊢
  generalize natBitLength (CAP * 32 - 1) = NB2 at a11 ⊢
  generalize natBitLength (Y * 2 - 1) = NB1 at a10 ⊢
  have hmx : max NB2 NB1 ≤ CAP * 32 + Y * 2 + 1 := by clear * - a10 a11; omega
  generalize max NB2 NB1 = MX at hmx ⊢
  generalize Nat.clog 2 (P.n + 2) = L at a8 a12 ⊢
  generalize fe * L = FL at a8 ⊢
  have hx : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  generalize P.n - P.r * P.b = XX at hx ⊢
  have d1 : (XX + 1) / 2 ≤ XX + 1 := Nat.div_le_self _ _
  have d2 : XX / 2 ≤ XX := Nat.div_le_self _ _
  have d3 : (XX + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d4 : XX % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d5 : FL / 4 ≤ FL := Nat.div_le_self _ _
  have d6 : FL % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have d7 : P.r / 2 ≤ P.r := Nat.div_le_self _ _
  generalize (XX + 1) / 2 = D1 at d1 ⊢
  generalize XX / 2 = D2 at d2 ⊢
  generalize (XX + 1) % 2 = D3 at d3 ⊢
  generalize XX % 2 = D4 at d4 ⊢
  generalize FL / 4 = D5 at d5 ⊢
  generalize FL % 4 = D6 at d6 ⊢
  generalize P.r / 2 = D7 at d7 a6 a7 ⊢
  clear * - a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hmb hmx hx d1 d2 d3 d4 d5 d6 d7
  omega

theorem tB2b_le (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe mb nc c0 c1 : ℕ) (hmb : mb ≤ 1) :
    tB2b P h0 h1 Cδ C m fe mb nc c0 c1 ≤ 10 ^ 6 * ((P.n + 1) ^ 26 + Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + fe * (2 * P.n + 4) + P.n * P.n + c0 + c1 + nc + 10) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := atoms P fe (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
  unfold tB2b
  generalize (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) = CAP at a11 ⊢
  generalize (P.n + 1) ^ 26 = Y at a9 a10 ⊢
  generalize natBitLength (CAP * 32 - 1) = NB2 at a11 ⊢
  generalize natBitLength (Y * 2 - 1) = NB1 at a10 ⊢
  have hmx : max NB2 NB1 ≤ CAP * 32 + Y * 2 + 1 := by clear * - a10 a11; omega
  generalize max NB2 NB1 = MX at hmx ⊢
  generalize Nat.clog 2 (P.n + 2) = L at a8 a12 ⊢
  generalize fe * L = FL at a8 ⊢
  have hx : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  generalize P.n - P.r * P.b = XX at hx ⊢
  have d1 : (XX + 1) / 2 ≤ XX + 1 := Nat.div_le_self _ _
  have d2 : XX / 2 ≤ XX := Nat.div_le_self _ _
  have d3 : (XX + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d4 : XX % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d5 : FL / 4 ≤ FL := Nat.div_le_self _ _
  have d6 : FL % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have d7 : P.r / 2 ≤ P.r := Nat.div_le_self _ _
  generalize (XX + 1) / 2 = D1 at d1 ⊢
  generalize XX / 2 = D2 at d2 ⊢
  generalize (XX + 1) % 2 = D3 at d3 ⊢
  generalize XX % 2 = D4 at d4 ⊢
  generalize FL / 4 = D5 at d5 ⊢
  generalize FL % 4 = D6 at d6 ⊢
  generalize P.r / 2 = D7 at d7 a6 a7 ⊢
  clear * - a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hmb hmx hx d1 d2 d3 d4 d5 d6 d7
  omega

theorem tB2c_le (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe mb nc c0 c1 : ℕ) (hmb : mb ≤ 1) :
    tB2c P h0 h1 Cδ C m fe mb nc c0 c1 ≤ 10 ^ 6 * ((P.n + 1) ^ 26 + Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + fe * (2 * P.n + 4) + P.n * P.n + c0 + c1 + nc + 10) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := atoms P fe (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
  unfold tB2c
  generalize (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) = CAP at a11 ⊢
  generalize (P.n + 1) ^ 26 = Y at a9 a10 ⊢
  generalize natBitLength (CAP * 32 - 1) = NB2 at a11 ⊢
  generalize natBitLength (Y * 2 - 1) = NB1 at a10 ⊢
  have hmx : max NB2 NB1 ≤ CAP * 32 + Y * 2 + 1 := by clear * - a10 a11; omega
  generalize max NB2 NB1 = MX at hmx ⊢
  generalize Nat.clog 2 (P.n + 2) = L at a8 a12 ⊢
  generalize fe * L = FL at a8 ⊢
  have hx : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  generalize P.n - P.r * P.b = XX at hx ⊢
  have d1 : (XX + 1) / 2 ≤ XX + 1 := Nat.div_le_self _ _
  have d2 : XX / 2 ≤ XX := Nat.div_le_self _ _
  have d3 : (XX + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d4 : XX % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d5 : FL / 4 ≤ FL := Nat.div_le_self _ _
  have d6 : FL % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have d7 : P.r / 2 ≤ P.r := Nat.div_le_self _ _
  generalize (XX + 1) / 2 = D1 at d1 ⊢
  generalize XX / 2 = D2 at d2 ⊢
  generalize (XX + 1) % 2 = D3 at d3 ⊢
  generalize XX % 2 = D4 at d4 ⊢
  generalize FL / 4 = D5 at d5 ⊢
  generalize FL % 4 = D6 at d6 ⊢
  generalize P.r / 2 = D7 at d7 a6 a7 ⊢
  clear * - a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hmb hmx hx d1 d2 d3 d4 d5 d6 d7
  omega

theorem tC1_le (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe mb nc c0 c1 : ℕ) (hmb : mb ≤ 1) :
    tC1 P h0 h1 Cδ C m fe mb nc c0 c1 ≤ 10 ^ 6 * ((P.n + 1) ^ 26 + Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + fe * (2 * P.n + 4) + P.n * P.n + c0 + c1 + nc + 10) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := atoms P fe (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
  unfold tC1
  generalize (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) = CAP at a11 ⊢
  generalize (P.n + 1) ^ 26 = Y at a9 a10 ⊢
  generalize natBitLength (CAP * 32 - 1) = NB2 at a11 ⊢
  generalize natBitLength (Y * 2 - 1) = NB1 at a10 ⊢
  have hmx : max NB2 NB1 ≤ CAP * 32 + Y * 2 + 1 := by clear * - a10 a11; omega
  generalize max NB2 NB1 = MX at hmx ⊢
  generalize Nat.clog 2 (P.n + 2) = L at a8 a12 ⊢
  generalize fe * L = FL at a8 ⊢
  have hx : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  generalize P.n - P.r * P.b = XX at hx ⊢
  have d1 : (XX + 1) / 2 ≤ XX + 1 := Nat.div_le_self _ _
  have d2 : XX / 2 ≤ XX := Nat.div_le_self _ _
  have d3 : (XX + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d4 : XX % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d5 : FL / 4 ≤ FL := Nat.div_le_self _ _
  have d6 : FL % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have d7 : P.r / 2 ≤ P.r := Nat.div_le_self _ _
  generalize (XX + 1) / 2 = D1 at d1 ⊢
  generalize XX / 2 = D2 at d2 ⊢
  generalize (XX + 1) % 2 = D3 at d3 ⊢
  generalize XX % 2 = D4 at d4 ⊢
  generalize FL / 4 = D5 at d5 ⊢
  generalize FL % 4 = D6 at d6 ⊢
  generalize P.r / 2 = D7 at d7 a6 a7 ⊢
  clear * - a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hmb hmx hx d1 d2 d3 d4 d5 d6 d7
  omega

theorem tC2_le (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe mb nc c0 c1 : ℕ) (hmb : mb ≤ 1) :
    tC2 P h0 h1 Cδ C m fe mb nc c0 c1 ≤ 10 ^ 6 * ((P.n + 1) ^ 26 + Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + fe * (2 * P.n + 4) + P.n * P.n + c0 + c1 + nc + 10) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := atoms P fe (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
  unfold tC2
  generalize (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) = CAP at a11 ⊢
  generalize (P.n + 1) ^ 26 = Y at a9 a10 ⊢
  generalize natBitLength (CAP * 32 - 1) = NB2 at a11 ⊢
  generalize natBitLength (Y * 2 - 1) = NB1 at a10 ⊢
  have hmx : max NB2 NB1 ≤ CAP * 32 + Y * 2 + 1 := by clear * - a10 a11; omega
  generalize max NB2 NB1 = MX at hmx ⊢
  generalize Nat.clog 2 (P.n + 2) = L at a8 a12 ⊢
  generalize fe * L = FL at a8 ⊢
  have hx : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  generalize P.n - P.r * P.b = XX at hx ⊢
  have d1 : (XX + 1) / 2 ≤ XX + 1 := Nat.div_le_self _ _
  have d2 : XX / 2 ≤ XX := Nat.div_le_self _ _
  have d3 : (XX + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d4 : XX % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d5 : FL / 4 ≤ FL := Nat.div_le_self _ _
  have d6 : FL % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have d7 : P.r / 2 ≤ P.r := Nat.div_le_self _ _
  generalize (XX + 1) / 2 = D1 at d1 ⊢
  generalize XX / 2 = D2 at d2 ⊢
  generalize (XX + 1) % 2 = D3 at d3 ⊢
  generalize XX % 2 = D4 at d4 ⊢
  generalize FL / 4 = D5 at d5 ⊢
  generalize FL % 4 = D6 at d6 ⊢
  generalize P.r / 2 = D7 at d7 a6 a7 ⊢
  clear * - a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hmb hmx hx d1 d2 d3 d4 d5 d6 d7
  omega

theorem tC3_le (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe mb nc c0 c1 : ℕ) (hmb : mb ≤ 1) :
    tC3 P h0 h1 Cδ C m fe mb nc c0 c1 ≤ 10 ^ 6 * ((P.n + 1) ^ 26 + Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + fe * (2 * P.n + 4) + P.n * P.n + c0 + c1 + nc + 10) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := atoms P fe (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
  unfold tC3
  generalize (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) = CAP at a11 ⊢
  generalize (P.n + 1) ^ 26 = Y at a9 a10 ⊢
  generalize natBitLength (CAP * 32 - 1) = NB2 at a11 ⊢
  generalize natBitLength (Y * 2 - 1) = NB1 at a10 ⊢
  have hmx : max NB2 NB1 ≤ CAP * 32 + Y * 2 + 1 := by clear * - a10 a11; omega
  generalize max NB2 NB1 = MX at hmx ⊢
  generalize Nat.clog 2 (P.n + 2) = L at a8 a12 ⊢
  generalize fe * L = FL at a8 ⊢
  have hx : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  generalize P.n - P.r * P.b = XX at hx ⊢
  have d1 : (XX + 1) / 2 ≤ XX + 1 := Nat.div_le_self _ _
  have d2 : XX / 2 ≤ XX := Nat.div_le_self _ _
  have d3 : (XX + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d4 : XX % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have d5 : FL / 4 ≤ FL := Nat.div_le_self _ _
  have d6 : FL % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have d7 : P.r / 2 ≤ P.r := Nat.div_le_self _ _
  generalize (XX + 1) / 2 = D1 at d1 ⊢
  generalize XX / 2 = D2 at d2 ⊢
  generalize (XX + 1) % 2 = D3 at d3 ⊢
  generalize XX % 2 = D4 at d4 ⊢
  generalize FL / 4 = D5 at d5 ⊢
  generalize FL % 4 = D6 at d6 ⊢
  generalize P.r / 2 = D7 at d7 a6 a7 ⊢
  clear * - a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hmb hmx hx d1 d2 d3 d4 d5 d6 d7
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm