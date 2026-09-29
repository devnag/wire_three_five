import Proof.Foundations.BooleanCircuitSizePadding
import Proof.Foundations.ComponentwiseValidity

/-!
# Executable componentwise-verifier parameters

The imported pointwise PCPP exposes real completeness and soundness constants,
whereas the fixed weak verifier can store and compare only finite rational
codes.  This module makes the one canonical rational choice and proves the
entire numerical reserve once.  Downstream machine code therefore receives
data, not an unproved real-comparison side condition.
-/

namespace NearCubicWires.ComponentwiseVerifierParameters

open NearCubicWires
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces

/-! ## Bounds derived from the executable PCPP source -/

theorem pointwiseSatisfiedFraction_le_one
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (auxiliary : BitInput pcpp.auxiliaryBits) :
    pcpp.satisfiedFraction input auxiliary ≤ 1 := by
  unfold PointwisePCPP.satisfiedFraction
  apply (div_le_one (by positivity)).2
  have hcard :
      (Finset.univ.filter fun i =>
        (pcpp.clauses i).eval
          (pcpp.assignment input auxiliary)).card ≤
        2 ^ pcpp.clauseBits := by
    simpa using
      (Finset.card_filter_le (Finset.univ : Finset (Fin (2 ^ pcpp.clauseBits)))
        (fun i => (pcpp.clauses i).eval
          (pcpp.assignment input auxiliary)))
  exact_mod_cast hcard

end NearCubicWires.ComponentwiseVerifierParameters
