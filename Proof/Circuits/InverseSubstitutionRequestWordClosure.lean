import Proof.Circuits.InverseSubstitutionRequestTail
import Proof.MachineModel.RuntimeCaseTwoDescriptionFrameAdapter

/-!
# The inverse substitution request word, without a schedule diagonal

The recovered oracle's circuit-code stream is paired with the selector-driven
three-field tail.  The tail computes its native width, scheduled source length,
and refuter word from the public target itself, so the old diagonal premise is
not needed.
-/

namespace NearCubicWires.InverseSubstitutionRequestWordClosure

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CanonicalDescriptionGroupingDecoder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorRequestSourceAdapter
open NearCubicWires.InverseSubstitutionRequestTail
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeCaseTwoRequestWordFrame
open NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure

/-! ## The closed encoder at one supplied atom stream -/

end NearCubicWires.InverseSubstitutionRequestWordClosure
