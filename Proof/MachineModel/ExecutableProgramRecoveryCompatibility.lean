import Proof.Foundations.OuterPCPRecovery

/-!
# Recovery compatibility for executable-program hierarchy sources

This is a consumer smoke test, not a public-contract edit.  It demonstrates
that a program-indexed PCP result and program-backed refuter source fill the
existing `HierarchyOuterPCP` and `FixedRefuterWitness` semantic consumers after
the one safe legacy projection.  No arbitrary-machine PCP guarantee is
reconstructed.
-/

namespace NearCubicWires.ExecutableProgramRecoveryCompatibility

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableProgramTimedSource
open NearCubicWires.ExecutableProgramTightRefuterSource
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces


end NearCubicWires.ExecutableProgramRecoveryCompatibility
