import Proof.Foundations.RecoveryScheduleEnvelope

/-!
# Canonical q-bit branch provenance

The outer split in this module is performed only after padding the hierarchy
PCP to the canonical width envelope.  Case 1 stores the literal failure of
every small q-bit accepting oracle and derives its amplifier input internally.
Case 2 stores the least accepting q-bit oracle and derives the one source PCPP
table on its native zero-face restriction.  Thus neither branch can substitute
an unrelated hard function, oracle, or occurrence table.
-/

namespace NearCubicWires.ScheduledRecovery

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PhysicalHardness
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduleArithmetic
open NearCubicWires.SourceInterfaces

/-- The sole padded outer PCP used by both branches. -/
def paddedOuterPCP
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    ProjectionPCP source.hierarchyMachine (pairClock clockDepth) :=
  padProjectionPCP outer.pcp.toSemantic
    (widthEnvelope outer) (nativeWidth_le_widthEnvelope outer)

@[simp] theorem paddedOuterPCP_nativeWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (n : ℕ) :
    (paddedOuterPCP outer).nativeWidth n = widthEnvelope outer n :=
  rfl

/-! ## Selector provenance -/

end NearCubicWires.ScheduledRecovery
