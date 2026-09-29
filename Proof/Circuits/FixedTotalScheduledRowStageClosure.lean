import Proof.CaseAnalysis.FixedSelectorCaseOnePointRunsOfRow
import Proof.MachineModel.BankScheduledRowStageClosure
import Proof.MachineModel.TotalOuterProofRowGuardedProgram

/-!
# The fixed scheduled row without query-count positivity

The generic guarded row emitter is interpreted at the published fixed schedule.
At zero query count the semantic decision row is empty; at nonzero count the
generic module already proves equality with the original row program.  This
module exposes only the unconditional fixed row contract and its immediate
Case-one point-run consumer.
-/

namespace NearCubicWires.FixedTotalScheduledRowStageClosure

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedRegisterCaseOneChain
open NearCubicWires.FixedScheduleDiagonalClosure
open NearCubicWires.FixedSelectorCaseOnePointRunsOfRow
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.OuterProofRowProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TotalOuterProofRowGuardedProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The semantic seam at zero -/

/-! ## 2. Fixed scheduled wrappers -/

/-! ## 3. Unconditional row and immediate point run -/


end NearCubicWires.FixedTotalScheduledRowStageClosure
