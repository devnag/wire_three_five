import Proof.MachineModel.CanonicalPaddedAmplifierEvaluationProgram
import Proof.MachineModel.CanonicalBooleanizeProgram
import Proof.MachineModel.CanonicalTaggedParityProgram
import Proof.MachineModel.TaggedProgramChoice

/-!
# One fixed target-bit evaluator

The target language has one executable entry point.  Tag zero invokes the
published Case-1 amplifier evaluator after canonical low-bit truncation; every
nonzero tag XORs the already evaluated Case-2 seed blocks.  A single final
suffix normalizes either branch to `0` or `1`, so no caller can attach a
different Boolean convention to an imported evaluator's nonzero output.
-/

namespace NearCubicWires.CanonicalTargetBitProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanizeProgram
open NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram
open NearCubicWires.CanonicalTaggedParityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

end NearCubicWires.CanonicalTargetBitProgram
