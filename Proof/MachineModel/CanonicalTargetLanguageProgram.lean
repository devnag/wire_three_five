import Proof.MachineModel.CanonicalTargetBitProgram
import Proof.Amplification.CaseTwoRecoveryAssembly
import Proof.CaseAnalysis.CaseTwoSeedDeterminacy

namespace NearCubicWires.CanonicalTargetLanguageProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoSeedDeterminacy
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UnaryPolynomialSelector
open NearCubicWires.VerifiedLinker

/-! ## 1. Exponential packaging of one exact interpreter run -/

/-! ## 2. The published refuter reads only the machine description -/

/-! ## 3. The Case-1/Case-2 split is one SAT query -/

/-! ## 4. The Case-2 seed comes from the published factory -/

/-! ### From the seed function to one seed bit -/

/-! ## 5. Both branches of the fixed dispatcher compute the branch core -/

/-! ## 6. Exact Case-1 execution of the canonical target bit -/

end NearCubicWires.CanonicalTargetLanguageProgram
