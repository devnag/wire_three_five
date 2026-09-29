import Mathlib

/-!
# S7: unnormalized masked expectations

Paper3's primitive estimates the *unnormalized* masked mean `E[M·f]` (P3:3087, 3455-3466); soundness
uses monotonicity under a Boolean mask (P3:3538-3542); completeness charges the discarded mass once
(P3:3439-3449).  Finite uniform spaces only, as in the Theorem 2.5 repository (`SupplierList.realMean`, `booleanMean`).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared

/-- Uniform mean over a finite type; definitionally the Theorem 2.5 repository's `SupplierList.realMean`. -/
noncomputable def uMean {Ω : Type} [Fintype Ω] (f : Ω → ℝ) : ℝ := (∑ ω, f ω) / Fintype.card Ω

/-- `0/1` as a real (the Theorem 2.5 repository's `bitAsReal`, restated to keep S7 Mathlib-only; the bridge is `rfl`). -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

/-- The unnormalized masked mean `E[M·f]` (`prim:truth`, P3:3087; `tr:tests`, P3:3476-3480). -/
noncomputable def maskedMean {Ω : Type} [Fintype Ω] (M : Ω → Bool) (f : Ω → ℝ) : ℝ :=
  uMean fun ω => bitR (M ω) * f ω

theorem bitR_nonneg (b : Bool) : 0 ≤ bitR b := by cases b <;> simp [bitR]
theorem bitR_le_one (b : Bool) : bitR b ≤ 1 := by cases b <;> simp [bitR]

theorem uMean_mono {Ω : Type} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) : uMean f ≤ uMean g := by
  unfold uMean
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω) (Nat.cast_nonneg _)

theorem uMean_add {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) : uMean (fun ω => f ω + g ω) = uMean f + uMean g := by
  unfold uMean; rw [Finset.sum_add_distrib, add_div]

/-- The unmasked lemmas are the `M = 1` instances (the §13.4 S7 gate). -/
theorem maskedMean_true {Ω : Type} [Fintype Ω] (f : Ω → ℝ) : maskedMean (fun _ => true) f = uMean f := by
  simp [maskedMean, bitR]

/-- Masking can only decrease a nonnegative score (`tr:one-sided`, P3:3538-3542). -/
theorem maskedMean_le_of_nonneg {Ω : Type} [Fintype Ω] (M : Ω → Bool) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    maskedMean M f ≤ uMean f :=
  uMean_mono fun ω => by
    have := bitR_le_one (M ω); have := hf ω; nlinarith

/-- Discrete Markov: `E[p·1[R > B]] ≤ E[p·R]/B` for `R ≥ 0` (`prim:ledger` P3:3213-3216; `tr:missing` P3:3440-3443). -/
theorem markov_indicator {Ω : Type} [Fintype Ω] (R : Ω → ℝ) (hR : ∀ ω, 0 ≤ R ω) {B : ℝ} (hB : 0 < B) :
    uMean (fun ω => bitR (decide (B < R ω))) ≤ uMean R / B := by
  have : uMean (fun ω => bitR (decide (B < R ω))) ≤ uMean (fun ω => R ω / B) := by
    apply uMean_mono; intro ω
    by_cases h : B < R ω
    · simp [bitR, h]; rw [le_div_iff₀ hB]; linarith
    · simp [bitR, h]; exact div_nonneg (hR ω) hB.le
  calc _ ≤ uMean (fun ω => R ω / B) := this
    _ = uMean R / B := by unfold uMean; rw [← Finset.sum_div, div_div, div_div, mul_comm]

/-- Masked error of a Boolean row lookup (`row:masked-error`, P3:2678-2701; `filt:observable` P3:2355-2383):
off the list-failure event and inside the population cap the reported and true lookups agree; above the cap
the regular filter accepts with mean at most `ξ`.  No term proportional to the measure of `{w > B}` appears. -/
def MaskedRowError {Ω : Type} [Fintype Ω] (G : Ω → Bool) (reported truth : Ω → Bool)
    (listFails overCap : Ω → Bool) (δ ξ : ℝ) : Prop :=
  (∀ ω, overCap ω = false → listFails ω = false → reported ω = truth ω) →
  uMean (fun ω => bitR (listFails ω && !overCap ω)) ≤ δ →
  uMean (fun ω => bitR (G ω && overCap ω)) ≤ ξ →
  uMean (fun ω => bitR (G ω) * |bitR (reported ω) - bitR (truth ω)|) ≤ δ + ξ

theorem maskedRowError_holds {Ω : Type} [Fintype Ω] (G : Ω → Bool) (reported truth : Ω → Bool)
    (listFails overCap : Ω → Bool) (δ ξ : ℝ) : MaskedRowError G reported truth listFails overCap δ ξ := by
  intro hagree hδ hξ
  have hpt : ∀ ω, bitR (G ω) * |bitR (reported ω) - bitR (truth ω)| ≤
      bitR (listFails ω && !overCap ω) + bitR (G ω && overCap ω) := by
    intro ω
    cases hG : G ω <;> cases hL : listFails ω <;> cases hO : overCap ω <;>
      cases hR : reported ω <;> cases hT : truth ω <;> simp_all [bitR]
  calc _ ≤ uMean (fun ω => bitR (listFails ω && !overCap ω) + bitR (G ω && overCap ω)) := uMean_mono hpt
    _ = _ := uMean_add _ _
    _ ≤ δ + ξ := add_le_add hδ hξ

/-- Masked Cauchy–Schwarz, the engine of `tr:rounding` (P3:3526-3531) and `tr:completeness` (P3:3602-3605). -/
theorem maskedMean_abs_mul_le {Ω : Type} [Fintype Ω] (M : Ω → Bool) (a b : Ω → ℝ) :
    maskedMean M (fun ω => |a ω * b ω|) ≤
      Real.sqrt (maskedMean M fun ω => a ω ^ 2) * Real.sqrt (maskedMean M fun ω => b ω ^ 2) := by
  unfold maskedMean uMean
  have hc : (0 : ℝ) ≤ Fintype.card Ω := Nat.cast_nonneg _
  rcases eq_or_lt_of_le hc with h0 | hpos
  · simp [← h0]
  have key : (∑ ω, bitR (M ω) * |a ω * b ω|) ≤
      Real.sqrt (∑ ω, bitR (M ω) * a ω ^ 2) * Real.sqrt (∑ ω, bitR (M ω) * b ω ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun ω => Real.sqrt (bitR (M ω)) * |a ω|) (fun ω => Real.sqrt (bitR (M ω)) * |b ω|)
    have e1 : ∀ ω, (Real.sqrt (bitR (M ω)) * |a ω|) * (Real.sqrt (bitR (M ω)) * |b ω|) =
        bitR (M ω) * |a ω * b ω| := by
      intro ω
      calc (Real.sqrt (bitR (M ω)) * |a ω|) * (Real.sqrt (bitR (M ω)) * |b ω|)
          = (Real.sqrt (bitR (M ω))) ^ 2 * (|a ω| * |b ω|) := by ring
        _ = bitR (M ω) * |a ω * b ω| := by rw [Real.sq_sqrt (bitR_nonneg _), abs_mul]
    have e2 : ∀ (c : Ω → ℝ) ω, (Real.sqrt (bitR (M ω)) * |c ω|) ^ 2 = bitR (M ω) * c ω ^ 2 := by
      intro c ω; rw [mul_pow, Real.sq_sqrt (bitR_nonneg _), sq_abs]
    simp only [e1, e2] at h
    have hl : 0 ≤ ∑ ω, bitR (M ω) * |a ω * b ω| :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (bitR_nonneg _) (abs_nonneg _)
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun ω _ => mul_nonneg (bitR_nonneg _) (sq_nonneg _))]
    exact Real.le_sqrt_of_sq_le h
  rw [Real.sqrt_div' _ hpos.le, Real.sqrt_div' _ hpos.le, div_mul_div_comm, Real.mul_self_sqrt hpos.le]
  exact div_le_div_of_nonneg_right key hpos.le

end NearCubicWires.WireExponent3_5.Shared
