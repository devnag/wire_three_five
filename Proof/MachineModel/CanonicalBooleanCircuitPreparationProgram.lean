import Proof.MachineModel.CanonicalBalancedLengthProgram
import Proof.MachineModel.CanonicalBooleanNodeBatchProgram
import Proof.Circuits.CanonicalForkCall

/-!
# Canonical Boolean-circuit preparation

One in-machine fork derives the exact balanced-list length and the validated
node-descriptor tree from the same canonical node word.  The topology pass
therefore receives a machine-derived count paired with the sole structural
descriptor stream; neither value can be supplied independently by a caller.
-/

namespace NearCubicWires.CanonicalBooleanCircuitPreparationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.ExecutableInterfaces

end NearCubicWires.CanonicalBooleanCircuitPreparationProgram
