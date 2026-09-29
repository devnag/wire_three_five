import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.TaggedProgramChoice

/-!
# Canonical heterogeneous fork call

Many validators must derive two independent facts from the same canonical
word.  This adapter tags two in-machine copies, dispatches them through the
existing fixed choice program, and reuses the sole paired-call controller.
The caller supplies neither a duplicated value nor an intermediate result.
-/

namespace NearCubicWires.CanonicalForkCall

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

end NearCubicWires.CanonicalForkCall
