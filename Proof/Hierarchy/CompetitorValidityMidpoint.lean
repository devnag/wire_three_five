import Proof.Hierarchy.CompetitorReusableDecision

/-! Literal C.10 decision parent: the mean test, every second-moment test,
and the acceptance midpoint are one executed ordinary list computation.
Its input records contain the actually produced exact signed fractions. -/
namespace NearCubicWires.RepairOrdinary.CompetitorValidity
open LocalBitMultitape RepairRepresentation RepairSource
open RepairSource.CompetitorRationalGap CompetitorThresholdDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Estimate where
  positive : ℕ
  negative : ℕ
  denominator : ℕ
def Estimate.value (a : Estimate) : ℚ := ((a.positive : ℚ)-a.negative)/a.denominator
structure Estimate.Valid (a : Estimate) (b : ℕ) : Prop where
  positive : a.positive<2^b
  negative : a.negative<2^b
  denominator : a.denominator<2^b
  denominatorPositive : 0<a.denominator

end NearCubicWires.RepairOrdinary.CompetitorValidity
