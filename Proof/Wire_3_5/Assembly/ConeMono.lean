import Statement_Wire_3_5

/-! # Monotonicity of Theorem 1.1 in its parameters

`wireExponent3_5_mono`: `WireExponent3_5 c' K'_T K'_S` implies `WireExponent3_5 c K_T K_S` whenever `c ≤ c'`,
`K'_T ≤ K_T` and `K'_S ≤ K_S`, with the same language and the same onsets. The proof uses `L(n) = ⌈log₂(n+2)⌉ ≥ 1` at
every `n`: then `L(n)^{K_T} ≥ L(n)^{K'_T}`, so every circuit within the cap `A n^{7/2}/L(n)^{K_T}` is within
`A n^{7/2}/L(n)^{K'_T}`, and `L(n)^{-c'} ≤ L(n)^{-c}`, so agreement below `1/2 + L(n)^{-c'}` is below
`1/2 + L(n)^{-c}`.

`rowBCone_of_rowB`: row B implies Theorem 1.1 on the cone above it (`rowBCone`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5

/-- `L(n) = ⌈log₂(n+2)⌉ ≥ 1` at every `n`. -/
theorem one_le_clog (n : ℕ) : (1 : ℝ) ≤ (Nat.clog 2 (n + 2) : ℝ) := by
  have h : 0 < Nat.clog 2 (n + 2) := Nat.clog_pos (by norm_num) (by omega)
  exact_mod_cast h

/-- A cap with a larger log exponent is smaller: `A n^{7/2}/L^K ≤ A n^{7/2}/L^{K'}` for `K' ≤ K`, `A > 0`. -/
theorem cap_le (A : ℝ) (hA : 0 < A) (n : ℕ) {K K' : ℝ} (hK : K' ≤ K) :
    A * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ K ≤
      A * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ K' := by
  have hL := one_le_clog n
  have hpos : (0 : ℝ) < (Nat.clog 2 (n + 2) : ℝ) ^ K' := Real.rpow_pos_of_pos (by linarith) _
  exact div_le_div_of_nonneg_left (mul_nonneg hA.le (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hpos
    (Real.rpow_le_rpow_of_exponent_le hL hK)

/-- A larger advantage exponent gives a smaller advantage: `L^{-c'} ≤ L^{-c}` for `c ≤ c'`. -/
theorem adv_le (n : ℕ) {c c' : ℝ} (hc : c ≤ c') :
    (Nat.clog 2 (n + 2) : ℝ) ^ (-c') ≤ (Nat.clog 2 (n + 2) : ℝ) ^ (-c) :=
  Real.rpow_le_rpow_of_exponent_le (one_le_clog n) (by linarith)

/-- **Monotonicity of Theorem 1.1**: `WireExponent3_5 c' K'_T K'_S → WireExponent3_5 c K_T K_S` for `c ≤ c'`,
`K'_T ≤ K_T`, `K'_S ≤ K_S` (a larger allowed advantage and smaller caps), with the same language. -/
theorem wireExponent3_5_mono {c KT KS c' KT' KS' : ℝ} (hc : c ≤ c') (hT : KT' ≤ KT) (hS : KS' ≤ KS)
    (h : _root_.NearCubicWires.WireExponent3_5 c' KT' KS') : _root_.NearCubicWires.WireExponent3_5 c KT KS := by
  obtain ⟨language, henp, hhard⟩ := h
  refine ⟨language, henp, ?_⟩
  unfold _root_.NearCubicWires.WireExponent3_5.WireExponent3_5Hard at hhard ⊢
  intro AT AS hAT hAS
  obtain ⟨onset, hon⟩ := hhard AT AS hAT hAS
  refine ⟨onset, fun n hn => ?_⟩
  obtain ⟨hthr, hsym⟩ := hon n hn
  have hadv := adv_le n hc
  refine ⟨fun circuit hw => ?_, fun circuit hw => ?_⟩
  · exact lt_of_lt_of_le (hthr circuit (hw.trans (cap_le AT hAT n hT))) (by linarith)
  · exact lt_of_lt_of_le (hsym circuit (hw.trans (cap_le AS hAS n hS))) (by linarith)

/-- **Row B implies Theorem 1.1 on the cone above row B.** -/
theorem rowBCone_of_rowB (h : _root_.NearCubicWires.WireExponent3_5.rowB) : rowBCone :=
  fun _ _ _ _ hc hT hS => wireExponent3_5_mono hc hT hS h

end NearCubicWires.WireExponent3_5
