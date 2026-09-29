import Proof.Circuits.InverseLengthStage
import Proof.MachineModel.RuntimeCaseTwoOccurrencePacketSplit

/-!
# The inverse occurrence schedule quad at the selector-driven length

The inverse length program computes the selected source length from the public
target.  A native call then runs the frozen occurrence-quad program at that
length.  This supplies the four schedule numerals without identifying the
public target with the scheduled source length.
-/

namespace NearCubicWires.InverseSelectorOccurrenceQuad

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseLengthStage
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.RuntimeScheduleQuadNumeralProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## Pair the selector quad with an oracle triple -/

end NearCubicWires.InverseSelectorOccurrenceQuad
