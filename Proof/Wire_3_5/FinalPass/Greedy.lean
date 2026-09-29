import Proof.Wire_3_5.FinalPass.Hash

/-! # Final pass: the greedy seed fixing over a rational objective (P3:2220-2231, 2238-2251)

Realizes the computable form of `filt:soft`'s greedy hash (P3:2238-2251): "fix the seed bits one at a time by the method
of conditional expectations [...] with exact rational arithmetic", where the objective `𝒰(h) = E_x a(x)H_h(x)` is a
rational number (a finite average of rational window powers). The real-valued greedy of M6 (`Filters.greedy`) compares
real averages; on an objective that is the cast of a rational function it makes the same choices as the rational
greedy (`greedyQ`), because the cast preserves averages and order.

Paper quantities: the rational mean `qMean` (`E`), the rational greedy `greedyQ`. Results: `uMean_cast` (the real mean of a
cast is the cast of the rational mean) and **`greedy_cast`** (`greedy m (Φ : ℝ) = greedyQ m Φ`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters

/-- The uniform mean over a finite type, in `ℚ`. -/
def qMean {Ω : Type} [Fintype Ω] (f : Ω → ℚ) : ℚ := (∑ ω, f ω) / Fintype.card Ω

theorem uMean_cast {Ω : Type} [Fintype Ω] (f : Ω → ℚ) : uMean (fun ω => (f ω : ℝ)) = ((qMean f : ℚ) : ℝ) := by
  unfold uMean qMean
  push_cast
  rfl

/-- **The greedy seed fixing over a rational objective** (P3:2238-2251): fix the first bit to the value whose
conditional mean is smaller (ties to `false`), then recurse. -/
def greedyQ : (m : ℕ) → ((Fin m → Bool) → ℚ) → (Fin m → Bool)
  | 0, _ => Fin.elim0
  | m + 1, Φ =>
    if qMean (fun s => Φ (Fin.cons false s)) ≤ qMean (fun s => Φ (Fin.cons true s)) then
      Fin.cons false (greedyQ m fun s => Φ (Fin.cons false s))
    else Fin.cons true (greedyQ m fun s => Φ (Fin.cons true s))

/-- **The real greedy on a rational objective is the rational greedy.** -/
theorem greedy_cast : ∀ (m : ℕ) (Φ : (Fin m → Bool) → ℚ), greedy m (fun s => (Φ s : ℝ)) = greedyQ m Φ
  | 0, _ => rfl
  | m + 1, Φ => by
    unfold greedy greedyQ
    simp only
    have hf := uMean_cast (fun s => Φ (Fin.cons false s))
    have ht := uMean_cast (fun s => Φ (Fin.cons true s))
    by_cases h : qMean (fun s => Φ (Fin.cons false s)) ≤ qMean (fun s => Φ (Fin.cons true s))
    · rw [if_pos h, if_pos (by rw [hf, ht]; exact_mod_cast h), greedy_cast m]
    · rw [if_neg h, if_neg (by rw [hf, ht]; exact_mod_cast h), greedy_cast m]

end NearCubicWires.WireExponent3_5.FinalPass
