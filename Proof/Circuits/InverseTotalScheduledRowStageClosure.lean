import Proof.Circuits.FixedTotalScheduledRowStageClosure
import Proof.CaseAnalysis.SelectorDrivenRegisterCaseOneChain

/-!
# The inverse scheduled row without query-count positivity

The total row emitter is schedule-agnostic.  Specializing it at the inverse
source index gives `InverseScheduledRowRuns` for every query count, including
zero.  Together with the direct selector-register Case-one theorem, this
removes both the old positivity premise and the old schedule diagonal.
-/

namespace NearCubicWires.InverseTotalScheduledRowStageClosure

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedTotalScheduledRowStageClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.OuterProofRowProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TotalOuterProofRowGuardedProgram

end NearCubicWires.InverseTotalScheduledRowStageClosure
