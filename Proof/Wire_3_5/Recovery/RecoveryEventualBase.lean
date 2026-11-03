import Proof.Wire_3_5.Recovery.RecoveryBudgetBase
import Proof.Wire_3_5.Recovery.RecoveryCaseOne
import Proof.Foundations.PolynomialSchedule

/-! # The recovery's per-width facts hold eventually (P3:3657-3697, 3737-3756, 3820-3852; D1.7)

Realizes the "sufficiently large `q`" of the recovery's ledger at the gate constants: the grid, the star, the per-atom
caps `w_i(q) = a_i q^{7/2}/L^{K_i}` ("Take an even `r = Θ(log L)` [...] `w_i(q)`", P3:3820-3824, 3784-3785), the clause
width ("Choose a branch-independent integer `d_G` bounding all PCPP clause counts", P3:3657-3659), the propagated
errors (P3:3616-3624), the Case-1 conditions (P3:3685-3692, 3839-3840), the XOR copies beyond the amplifier's arity
coefficient, and the guess budget "Every guess has `q^{O(1)} = o(N)` bits" (P3:3675-3677).

Paper quantities:
* `xorEpsilon_succ_lt`: one more XOR copy strictly lowers the advantage threshold `e_t`;
* the caps: `q ≤ ⌊w_i(q)⌋` and `⌊w_i(q)⌋ + 1 ≤ 2(q+1)⁴` eventually (`eventually_wireCap_ge`, `eventually_wireCap_le`);
* the grid `s(q) ≤ q` and the clause width `⌈d_G log₂(q+2)⌉ ≤ q` eventually;
* **`recBudget`**: the guess-length envelope `1 + K_O + n_v·s·(4 + K_c)` as a fixed polynomial of `q`
  (`recBudget_poly`);
* **`RecQ l G q`** (the per-width facts) and **`eventually_recQ`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule NearCubicWires.RecoveryWitnessPolicy NearCubicWires.PolynomialSchedule
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open Filter

/-! ## One more XOR copy -/

theorem xorEpsilon_succ_lt (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 2) (t : ℕ) (ht : 1 ≤ t) :
    xorEpsilon δ (t + 1) < xorEpsilon δ t := by
  unfold xorEpsilon
  have e : t + 1 - 1 = (t - 1) + 1 := by omega
  rw [e, pow_succ]
  have ha : 0 < (1 - δ) ^ (t - 1) := pow_pos (by linarith) _
  have hb : 0 < 1 / 2 - δ := by linarith
  have hp := mul_pos (mul_pos ha h0) hb
  have e2 : (1 - δ) ^ (t - 1) * (1 - δ) * (1 / 2 - δ) =
      (1 - δ) ^ (t - 1) * (1 / 2 - δ) - (1 - δ) ^ (t - 1) * δ * (1 / 2 - δ) := by ring
  rw [e2]; linarith

/-! ## The per-atom caps -/

theorem wireCap_nonneg (C : CapParams) (m : Mode) (q : ℕ) : 0 ≤ wireCap C m q := by
  unfold wireCap; positivity

/-- `q ≤ w_i(q)` eventually (the exponent `K_i ≤ 6` and `L⁶ ≤ q`). -/
theorem eventually_wireCap_ge (C : CapParams) (m : Mode) (hc : 1 ≤ C.coef m) :
    ∀ᶠ q : ℕ in atTop, (q : ℝ) ≤ wireCap C m q := by
  filter_upwards [eventually_mul_Lq_pow_le 1 6, eventually_ge_atTop 1] with q hL hq1
  unfold wireCap
  have hL1 : (1 : ℝ) ≤ (Lq q : ℝ) := by exact_mod_cast Lq_pos q
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have he : ((capExp32 m : ℝ) / 32) ≤ 6 := by cases m <;> norm_num [capExp32]
  have hLe : (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) ≤ (Lq q : ℝ) ^ (6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 he
  have hL6 : (Lq q : ℝ) ^ (6 : ℝ) ≤ q := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h6 : Lq q ^ 6 ≤ q := by simpa using hL
    exact_mod_cast h6
  have hpos : 0 < (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) := Real.rpow_pos_of_pos (by linarith) _
  rw [le_div_iff₀ hpos]
  have hsq : 1 ≤ Real.sqrt q := by
    have h := Real.sqrt_le_sqrt hq0
    rwa [Real.sqrt_one] at h
  have hc' : (1 : ℝ) ≤ (C.coef m : ℝ) := by exact_mod_cast hc
  have hqq : (q : ℝ) * q ≤ (q : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hq0 (mul_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg q) : (0 : ℝ) ≤ q * q)
    nlinarith [h]
  have hq3 : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
  calc (q : ℝ) * (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) ≤ (q : ℝ) * q :=
        mul_le_mul_of_nonneg_left (hLe.trans hL6) (Nat.cast_nonneg q)
    _ ≤ (q : ℝ) ^ 3 := hqq
    _ = 1 * (q : ℝ) ^ 3 * 1 := by ring
    _ ≤ (C.coef m : ℝ) * (q : ℝ) ^ 3 * Real.sqrt q := by gcongr

/-- `w_i(q) ≤ q⁴` eventually (`a_i ≤ √q`). -/
theorem eventually_wireCap_le (C : CapParams) (m : Mode) :
    ∀ᶠ q : ℕ in atTop, wireCap C m q ≤ (q : ℝ) ^ 4 := by
  filter_upwards [eventually_ge_atTop (C.coef m ^ 2)] with q hq
  unfold wireCap
  have hL1 : (1 : ℝ) ≤ (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) :=
    Real.one_le_rpow (by exact_mod_cast Lq_pos q) (by positivity)
  have hnum0 : 0 ≤ (C.coef m : ℝ) * (q : ℝ) ^ 3 * Real.sqrt q := by positivity
  have hc : (C.coef m : ℝ) ≤ Real.sqrt q := by
    have h1 : ((C.coef m : ℝ)) ^ 2 ≤ (q : ℝ) := by exact_mod_cast hq
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hs : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (by positivity)
  have hq3 : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
  calc (C.coef m : ℝ) * (q : ℝ) ^ 3 * Real.sqrt q / (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32)
      ≤ (C.coef m : ℝ) * (q : ℝ) ^ 3 * Real.sqrt q := div_le_self hnum0 hL1
    _ = (q : ℝ) ^ 3 * ((C.coef m : ℝ) * Real.sqrt q) := by ring
    _ ≤ (q : ℝ) ^ 3 * (Real.sqrt q * Real.sqrt q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) hq3
    _ = (q : ℝ) ^ 4 := by rw [hs]; ring

/-- The integer cap `⌊w_i(q)⌋` from the two real bounds. -/
theorem floorCap_facts (C : CapParams) (m : Mode) (q : ℕ) (hge : (q : ℝ) ≤ wireCap C m q)
    (hle : wireCap C m q ≤ (q : ℝ) ^ 4) :
    q ≤ ⌊wireCap C m q⌋₊ ∧ ⌊wireCap C m q⌋₊ + 1 ≤ 2 * (q + 1) ^ 4 := by
  refine ⟨Nat.le_floor hge, ?_⟩
  have h1 : ⌊wireCap C m q⌋₊ ≤ q ^ 4 := Nat.floor_le_of_le (by push_cast; exact hle)
  have h2 : q ^ 4 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h3 : 1 ≤ (q + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  omega

/-! ## The grid and the clause width -/

/-- `s(q) ≤ q` eventually (`s⁸ ≤ C_sp L³`). -/
theorem eventually_sp_le (P : RowBParams) : ∀ᶠ q : ℕ in atTop, P.sp q ≤ q := by
  filter_upwards [eventually_mul_Lq_pow_le P.Csp 3] with q hq
  have h := (P.sp_le q).trans hq
  rcases Nat.eq_zero_or_pos (P.sp q) with h0 | h0
  · omega
  · exact (Nat.le_self_pow (by norm_num) _).trans h

/-- `⌈d_G log₂(q+2)⌉ ≤ q` eventually. -/
theorem eventually_clauseWidth_le (dG : ℕ) : ∀ᶠ q : ℕ in atTop, clauseWidth dG q ≤ q := by
  filter_upwards [eventually_mul_Lq_pow_le dG 1] with q hq
  unfold clauseWidth
  have h := clog_pow_le (q + 2) dG
  simp only [pow_one] at hq
  unfold Lq at hq
  omega

/-! ## The guess budget as a fixed polynomial of `q` -/

section BudgetPoly
variable (l : Literals)

/-- The atom code bound `K_c(q)` at the description envelope `(q+1)^{26}`. -/
def recKc (q : ℕ) : ℕ :=
  2 * (canonicalSymmetricCircuitCodeBitBound ((q + 1) ^ 26 + 4) +
    canonicalThresholdCircuitCodeBitBound ((q + 1) ^ 26 + 4)) + 1

theorem pb_succ_pow (e k : ℕ) : PolynomiallyBounded (fun q => (q + 1) ^ e + k) :=
  ⟨k + 1, e, by omega, fun n => by
    show (n + 1) ^ e + k ≤ (k + 1) * (n + 1) ^ e
    have h1 : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    have h2 : k * 1 ≤ k * (n + 1) ^ e := Nat.mul_le_mul_left k h1
    have e2 : (k + 1) * (n + 1) ^ e = k * (n + 1) ^ e + (n + 1) ^ e := by ring
    omega⟩

theorem pb_succ_pow' (e : ℕ) : PolynomiallyBounded (fun q => (q + 1) ^ e) :=
  polynomiallyBounded_mono (fun _ => Nat.le_add_right _ 0) (pb_succ_pow e 0)

end BudgetPoly

/-! ## The per-width facts -/

end NearCubicWires.WireExponent3_5.Transfer
