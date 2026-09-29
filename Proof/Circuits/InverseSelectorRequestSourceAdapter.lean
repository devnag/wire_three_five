import Proof.Circuits.FixedDescriptionRequestSourceAdapter
import Proof.Circuits.InverseLengthStage
import Proof.MachineModel.RuntimeCaseTwoRequestWordFrame

/-!
# Inverse request source tail at the selector-driven schedule

This is the inverse counterpart of the fixed request-source adapter.  The
source-driven bank emits the inverse selector's own scheduled registers; the
register-driven refuter frame and public source-word adapter then return
`pair sourceLength refuterWord`.  No schedule diagonal is used.
-/

namespace NearCubicWires.InverseSelectorRequestSourceAdapter

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankRefuterWordFrameProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedDescriptionRequestSourceAdapter
open NearCubicWires.InverseLengthStage
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoRequestWordFrame
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

end NearCubicWires.InverseSelectorRequestSourceAdapter
