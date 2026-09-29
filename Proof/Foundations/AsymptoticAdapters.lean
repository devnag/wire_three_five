import Proof.Foundations.Semantics

/-!
# Exact asymptotic adapters for the headline boundary

These lemmas isolate the order-sensitive conversions used after canonical
recovery.  They deliberately operate on the concrete headline functions rather
than on an informal `O`-notation layer, so the final proof cannot silently lose
strictness or reverse a cap comparison.
-/

namespace NearCubicWires

theorem logScale_pos (n : ℕ) : 0 < logScale n := by
  exact Nat.clog_pos (by omega) (by omega)

theorem wireScale_mono_coefficient
    {smaller larger : ℝ} (hcoeff : smaller ≤ larger)
    (logExponent n : ℕ) :
    wireScale smaller logExponent n ≤
      wireScale larger logExponent n := by
  unfold wireScale
  gcongr

end NearCubicWires
