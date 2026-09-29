import Proof.MachineModel.CanonicalBitSliceProgram
import Proof.MachineModel.CanonicalSignedGateEvaluationProgram

namespace NearCubicWires.CanonicalSignedAtomRequestProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## §1 The coordinate frame

The generated range leaves one index beside a shared context.  For an atom
list that context is the gate's weight code, the requested sign, and the mask
whose digit selects the coordinate's bit. -/

/-! ## §2 The three straight-line adapters -/

/-! ## §3 The mask digit is the coordinate's bit -/

/-! ## §4 The per-coordinate atom stage

Five stages: frame the lookup, select the weight, frame the digit, read the
digit, assemble the request.  Only the two library stages do any work; the
three adapters are pure pair plumbing. -/

/-! ## §5 The atom the stage names

Instantiating the code list at a gate's canonical weight syntax identifies the
stage's output with `signedAtomRequest`, the balanced-call request the signed
accumulator of `CanonicalSignedGateEvaluationProgram` §4 consumes. -/

/-! ## §6 One masked accumulator's whole request list

The coordinate stage is uniform in the index, so the whole atom list of one
masked accumulator is the generated index range mapped through it.  Nothing
between the generator and the balanced call is new: the retained context is
dropped by one projection instruction. -/

/-! ## §7 The atom list the machine names

Instantiating the code list at a gate's canonical weight syntax identifies the
executed list with `signedAtomRequests` of `gateAtoms`: exactly the balanced
request list `run_signedAtomTotalProgram` consumes. -/

/-! ## §8 The frozen coordinate: two mask digits and one subtraction

`residualConstantLeftAtoms` and `residualConstantRightAtoms` select their
coordinates with `frozenSelector`, which is `AND NOT` of the input and live
digits.  On single bits saturating subtraction is exactly that, so the frozen
coordinate stage is the uniform stage with a second one-digit slice and one
`subtract` instruction.  Carrying the two masks as one pair leaves the lookup
frame of §2 untouched.

Taking the second mask to be zero recovers the uniform selector, so this one
machine covers every atom list of `CanonicalSignedGateEvaluationProgram`. -/

/-! ## §9 The frozen coordinate stage

Seven stages: frame the lookup, select the weight, frame and read the input
digit, frame and read the live digit, subtract and assemble.  Taking
`liveMask = 0` leaves the input digit untouched, so this machine also names the
uniform selectors of §4. -/

/-! ## §10 The atom list over an arbitrary coordinate stage

The generator, the projection, and the balanced call do not depend on which
coordinate stage is mapped, so the list builder takes that stage as a
link-time parameter with one contract per index.  `signedAtomRequestListProgram`
is the uniform instance of this program by definition. -/

/-! ## §11 The frozen atom list

The frozen instance of §10.  Its output is `signedAtomRequests` of
`gateAtoms gate wanted (frozenSelector inputMask liveMask)`: the coordinate
body of both `residualConstant` atom lists. -/

end NearCubicWires.CanonicalSignedAtomRequestProgram
