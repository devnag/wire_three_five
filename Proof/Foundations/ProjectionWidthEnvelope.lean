import Proof.Foundations.OuterPCPRecovery

/-!
# Source-only exact-width envelope for the outer projection PCP

The executable PCP may report an irregular native address width.  Its imported
proof-count bound nevertheless gives one canonical logarithmic width depending
only on the source length and fixed source constants.  Padding to this envelope
makes the recovery schedule branch-independent without assuming monotonicity of
the runner's decoded output.
-/

namespace NearCubicWires.ProjectionWidthEnvelope

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces

def widthBudget
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (sourceLength : ℕ) : ℕ :=
  outer.pcp.shape.coefficient * bound sourceLength *
    logScale (bound sourceLength) ^ outer.proofExponent

/-- The least binary logarithmic envelope justified by the source's explicit
proof-count budget. -/
def widthEnvelope
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (sourceLength : ℕ) : ℕ :=
  Nat.log 2 (widthBudget outer sourceLength)

theorem nativeWidth_le_widthEnvelope
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (sourceLength : ℕ) :
    outer.pcp.nativeWidth sourceLength ≤
      widthEnvelope outer sourceLength := by
  apply Nat.le_log_of_pow_le (by omega)
  exact outer.proofSizeBound sourceLength

theorem logScale_le_add_two (value : ℕ) :
    logScale value ≤ value + 2 := by
  unfold logScale
  exact Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)

end NearCubicWires.ProjectionWidthEnvelope
