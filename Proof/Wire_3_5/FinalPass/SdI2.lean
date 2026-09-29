import Proof.Wire_3_5.FinalPass.SdI1

/-! # S4 (the seeds phase), part 51: the numbers' width, polynomial in `n` (P3:2994-3000, 3044-3048)

The printed numerator is at most `ptCount·vmax = |centers|·|E|·Q·vmax` (`fpNum_le`), and each factor is `2^{poly(n)}`:
`|centers| = 2^{n−k}`, `|E| ≤ (n+2)^{gapZ}`, `vmax ≤ 2(n+2)^{ZV}`, and the sample count
`Q ≤ 2^{⌊(6kh+3)/4⌋}·n^{13 + C + 2D} ≤ 2^{2n²+1+n(13+C+2D)}` (`Sampler.sampleCount_le` at the index bound
`callIndex_le_sym/thr`). **`ptv_lt`**: `ptCount·vmax < 2^{Tf r}` at the width `Tf r = KT·(n+2)^{ZT}` (the constants
from the literals and the gate only). S4's counters run at this width; the front's `W` may be it.

Paper quantity of the main type: the width of the printed numerator (`fpNum < 2^{Tf}`, P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split

theorem mul4_le {a b c d x y z w : ℕ} (ha : a ≤ 2 ^ x) (hb : b ≤ 2 ^ y) (hc : c ≤ 2 ^ z) (hd : d ≤ 2 ^ w) :
    a * b * c * d ≤ 2 ^ (x + y + z + w) := by
  calc a * b * c * d ≤ 2 ^ x * 2 ^ y * 2 ^ z * 2 ^ w :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc) hd
    _ = _ := by rw [pow_add, pow_add, pow_add]

theorem le_two_pow_of {x b : ℕ} (h : x ≤ b) : x ≤ 2 ^ b :=
  h.trans (Nat.lt_two_pow_self).le

theorem card_prime_le (c : ℕ) : Fintype.card (PrimeIndex c) ≤ c + 1 := by
  rw [Fintype.card_coe]; exact RepairOrdinary.CloseoutFinalC10WireEnvelope.primesUpTo_card_le c

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

