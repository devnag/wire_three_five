import Proof.Circuits.InverseSelectorNativeWidth

/-!
# The inverse substitution request's three-field tail

Pairs the selector-scheduled native width with the already closed scheduled
source length/refuter-word stream.  All three fields are computed from the
public `(target,target)` state without a schedule diagonal.
-/

namespace NearCubicWires.InverseSubstitutionRequestTail

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorNativeWidth
open NearCubicWires.InverseSelectorRequestSourceAdapter
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.VerifiedLinker

end NearCubicWires.InverseSubstitutionRequestTail
