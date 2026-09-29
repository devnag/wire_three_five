import Proof.Hierarchy.CompetitorSourceAverage

/-! The fixed interior rational reserve absorbs the actual outer N^-10
acceptance mass. The midpoint consumer keeps the separate estimation and
rounding errors visible until the enclosing record producer supplies them. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open RepairSource RepairRepresentation SourceInterfaces PCPPRequestBoundary
open ProjectionPCPPadding CompetitorRationalGap
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem outer_error_onset {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    ∃ onset : ℕ,1 ≤ onset ∧ ∀ n,onset ≤ n →
      source.soundness+1/(n : ℝ)^10 ≤ (constants.soundness : ℝ) := by
  let reserve : ℝ := constants.soundness-source.soundness
  have hreserve : 0 < reserve := sub_pos.mpr constants.lower
  obtain ⟨k,hk⟩ := exists_nat_gt (1/reserve)
  refine ⟨max 1 k,le_max_left _ _,?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_left 1 k) hn)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hkN : (k : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right 1 k) hn)
  have hrec : 1/(n : ℝ) ≤ reserve := by
    have h := one_div_le_one_div_of_le (one_div_pos.mpr hreserve) (hk.le.trans hkN)
    simpa only [one_div_one_div] using h
  have hpow : 1/(n : ℝ)^10 ≤ 1/(n : ℝ) :=
    one_div_le_one_div_of_le hn0 (le_self_pow₀ hn1 (by decide : (10 : ℕ) ≠ 0))
  have hle := hpow.trans hrec
  dsimp [reserve] at hle
  linarith

end NearCubicWires.RepairOrdinary.CompetitorSourceAverage
