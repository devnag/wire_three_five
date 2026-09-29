import Proof.Circuits.SelectorDrivenAtomContextRuns
import Proof.MachineModel.BankProjectionTableStage

/-!
# Projection table execution at the selector-driven frame

The selector frame contains the scheduled PCP input length, but the outer
request still has public length `target`.  The frozen table stage therefore
cannot be reused directly: its runner invocation requires those lengths to be
equal.  This adapter reads the scheduled length from the frame and invokes the
entire frozen table stage through the native-call ABI at that length.  No
schedule diagonal is required.
-/

namespace NearCubicWires.SelectorDrivenProjectionTableStage

open NearCubicWires
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Turn the selector frame into one native request -/

/-! ## 2. The relocated table stage -/

/-! ## 3. Site 3: the table residual, with no diagonal -/

end NearCubicWires.SelectorDrivenProjectionTableStage
