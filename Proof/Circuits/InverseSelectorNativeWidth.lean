import Proof.Circuits.InverseSelectorRequestSourceAdapter

/-!
# Native width at the inverse selector's scheduled source length

The published shape runner expects its own input length.  The outer request's
length is generally different, so this module calls it through the standard
native contextual call ABI after the executable inverse length stage.  This is
the native-width half of the inverse substitution-request tail and assumes no
schedule diagonal.
-/

namespace NearCubicWires.InverseSelectorNativeWidth

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedDescriptionRequestSourceAdapter
open NearCubicWires.InverseLengthStage
open NearCubicWires.InverseSelectorRequestSourceAdapter
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Frame the scheduled length as a contextual native call -/

/-! ## 2. Project the shape runner's native-width field -/

/-! ## 3. The scheduled native-width stream -/

end NearCubicWires.InverseSelectorNativeWidth
