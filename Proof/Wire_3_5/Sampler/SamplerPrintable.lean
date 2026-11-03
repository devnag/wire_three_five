import Proof.Wire_3_5.Sampler.SamplerFix
import Proof.Wire_3_5.Foundations.Runtime
import Proof.Wire_3_5.Compiler.Table

/-! # B6: `samp:printable` accounting — the sample count, the seed length, the load, the final pass (P3:2977-3055)

Realizes the accounting of `samp:printable`: "Choose `Q` as the ceiling in (samp:q), or the next power of two. Its
logarithm is `O_h(k+L)`, so the seed in samp:seed has that length [...] Its leading occurrence logarithm is
`O_h((k+L)²d + k + L²)` (samp:load) [...] With `h = 4` one can take `Q ≤ 2^{3k/4}n^{C'}`, for a constant `C'` fixed
independently of the subsequent choice of `r`. The final sampled observable is evaluable in `2^{n−k/4}poly(n)` time"
(P3:2987-3001), and the proof's "Substitution in (alg:eq-occurrences) gives
`log₂𝒮 ≤ O_h(k+L²) + O_h(k+L)·d·O(k+L)`, which is (samp:load)" (P3:3027-3031) and "For `h = 4`, (samp:q) is
`Q = O(N^{3/2}I^{1/4}η^{−2}) = 2^{3k/4}n^{O(1)}`" (P3:3043-3044), for the direct `h = 4` condition used here
(`Q⁴η⁸ ≥ 4⁸C₈·I·N⁵`, `Q = O(N^{5/4}I^{1/4}η^{−2})`).

Main declarations: **`sampleCount`** (`Q = 2^{⌈5kh/4⌉}·2^{13}·I·n^{2D}`) with **`sampleCount_rate`** (it meets
`4⁸C₈IN⁵ ≤ Q⁴η⁸` at `η = n^{−D}`), `N_le_sampleCount`, **`sampleCount_le`** (`Q ≤ 2^{⌈3k/4⌉}·n^{13+C+2D}`, C5's
precondition shape, `k = 2kh`); `ellFor`/`seedParamsFor` (the field size and generator parameters),
**`seedBits_le`** (the seed length `8ℓ ≤ 8(k + ⌈log₂Q⌉ + 1)`); **`samp_load`** (the compiled occurrence count is
`≤ 2^{C((k+L)²d + k + L²)}` when `A ≤ 2^{c(k+L²)}`, `m ≤ cL`, `Q' ≤ c(k+L)`, `P_ex+1 ≤ 2^{c(k+L)}`, with
`C = c + c + c + c²`); and **`final_pass_sampler`** (the final pass fits the seed's `final_pass_count`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.Shared

/-- **The sample count** at error `η = n^{−D}`, `I` matrix indices, `N = 2^{kh}`:
`Q = 2^{⌈5kh/4⌉}·2^{13}·I·n^{2D}`. -/
def sampleCount (kh D n I : ℕ) : ℕ := 2 ^ ((5 * kh + 3) / 4) * (2 ^ 13 * I * n ^ (2 * D))

theorem N_le_sampleCount (kh D n I : ℕ) (hn : 1 ≤ n) (hI : 1 ≤ I) : 2 ^ kh ≤ sampleCount kh D n I := by
  unfold sampleCount
  calc 2 ^ kh ≤ 2 ^ ((5 * kh + 3) / 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ ((5 * kh + 3) / 4) * 1 := (mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_pos (Nat.mul_pos (by norm_num) hI) (Nat.pow_pos hn))

/-- The field size of the generator: `ℓ = max(1, 2kh, ⌈log₂Q⌉)` (P3:2932). -/
def ellFor (kh Q : ℕ) : ℕ := max 1 (max (2 * kh) (Nat.clog 2 Q))

/-- The generator parameters for `N = 2^{kh}` and `Q` samples. -/
def seedParamsFor (kh Q : ℕ) : SeedParams where
  ell := ellFor kh Q
  kh := kh
  Q := Q
  one_le_ell := le_max_left _ _
  k_le := le_trans (le_max_left _ _) (le_max_right _ _)
  Q_le := (Nat.le_pow_clog (by norm_num) Q).trans
    (Nat.pow_le_pow_right (by norm_num) (le_trans (le_max_right _ _) (le_max_right _ _)))

end NearCubicWires.WireExponent3_5.Sampler
