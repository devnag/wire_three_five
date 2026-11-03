import Proof.MachineModel.BlockScrubEntry
import Proof.Assembly.RowProduction

namespace NearCubicWires.BlockPlatform
open LocalBitMultitape RepairOrdinary NearCubicWires.ExtDecompositionBatch RepairRepresentation
open ValidatorPolynomialDomination PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

namespace PolyBound


theorem one_le_pow (m d : ℕ) : 1 ≤ (m+1)^d := Nat.one_le_pow _ _ (Nat.succ_pos m)

/-! ## 1. Closure -/

/-- Sums at different degrees (the larger degree is taken). -/
theorem add {a b m ca cb da db : ℕ} (ha : PolyBounded a m ca da) (hb : PolyBounded b m cb db) :
    PolyBounded (a+b) m (ca+cb) (max da db) :=
  (ha.degree_mono (le_max_left _ _)).add (hb.degree_mono (le_max_right _ _))

/-- Constants are dominated at every degree. -/
theorem const (k m d : ℕ) : PolyBounded k m k d := polyBounded_const k m d

/-- **Monotone composition.** A charge polynomial in `S`, with `S` itself polynomial in `T`,
is polynomial in `T` (degrees multiply). -/
theorem comp {v S T c d c' d' : ℕ} (h : PolyBounded v S c d) (hS : PolyBounded S T c' d') :
    PolyBounded v T (c*(c'+1)^d) (d*d') := by
  unfold PolyBounded at h hS ⊢
  have h1 : S+1 ≤ (c'+1)*(T+1)^d' := by
    have := one_le_pow T d'
    nlinarith
  calc v ≤ c*(S+1)^d := h
    _ ≤ c*((c'+1)*(T+1)^d')^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
    _ = c*(c'+1)^d*(T+1)^(d*d') := by rw [mul_pow, ← pow_mul, Nat.mul_comm d' d]; ring

/-! ## 2. The driver: computed once, it covers the stage it serves -/

/-- The entry's driver for a stage cost `f ≤ c*(S+1)^d` is `(c+1)*(S+1)^d ≥ f+1`: exactly the
scrub premise `hR`, with `S` the parsed dimension. -/
theorem driver_covers {f S c d : ℕ} (h : PolyBounded f S c d) :
    f+1 ≤ UnaryCalc.value d (c+1) S := by
  unfold PolyBounded at h
  unfold UnaryCalc.value
  have := one_le_pow S d
  nlinarith

/-- `Scrub.entry`'s own cost is a fixed polynomial in the dimension (degree `D+1`). -/
theorem entryCost_polyBounded (D C n : ℕ) :
    PolyBounded (Scrub.entryCost D C n) n (UnaryCalc.polyCoefficient D C+4*C+12) (D+1) := by
  have hp := UnaryCalc.poly_cost_polyBounded D C n
  unfold PolyBounded at hp ⊢
  unfold Scrub.entryCost UnaryCalc.value
  have p := one_le_pow n (D+1)
  have hv : C*(n+1)^D ≤ C*(n+1)^(D+1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have e : (UnaryCalc.polyCoefficient D C+4*C+12)*(n+1)^(D+1) =
      UnaryCalc.polyCoefficient D C*(n+1)^(D+1)+4*(C*(n+1)^(D+1))+12*(n+1)^(D+1) := by ring
  omega

/-! ## 3. Exit into `packetBudget` (one family-row factor, any fixed power of `smallSize`) -/

/-! ## 4. Exit into `rowBudget`'s per-cell table factor -/

end PolyBound
end
end NearCubicWires.BlockPlatform
