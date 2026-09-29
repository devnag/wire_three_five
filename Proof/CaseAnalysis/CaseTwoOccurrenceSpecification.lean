import Proof.MachineModel.CanonicalTargetLanguageProgram

/-!
# The Case-2 seed bit as three factory-runner calls

`CanonicalTargetLanguageProgram.caseTwoSeed_apply` reduces one scheduled
Case-2 seed bit to one padded honest-occurrence value of the published PCPP
factory.  This module removes the last semantic wrapper from that value: the
`SourceHonestPCPPTable`, the choice hidden in `caseTwoTable`, and both padding
layers disappear, leaving exactly

* one `clauseRunner` call selecting the requested two-literal clause,
* one `supportRunner` call per systematic coordinate, folded by `parityOn`,
* one `honestRunner` call supplying the auxiliary block.

`caseTwoSeed_apply_executable` is therefore the precise contract that the
executable Case-2 occurrence evaluator has to meet: its right-hand side
mentions only `ExecutablePointwisePCPP` runner executions and one parity fold
over already decoded data.
-/

namespace NearCubicWires.CaseTwoOccurrenceSpecification

open NearCubicWires
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. One occurrence value of an executable pointwise PCPP -/

/-! ## 2. The scheduled Case-2 instance -/

end NearCubicWires.CaseTwoOccurrenceSpecification
