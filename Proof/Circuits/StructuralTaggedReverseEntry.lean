import Batteries.Tactic.OpenPrivate
import Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-!
# The tagged reverse pass at an arbitrary entry state

`structuralTaggedReverseProgram` is the `11`-instruction stream every scheduler
calls to turn its private reverse spine back into forward order.  It is
published only at `initialNPOracleState`, but a relocated call starts on
whatever registers the previous call left in the callee's frame, so callers one
level up need it at an arbitrary entry.

The controller reads register `7` once, at the loop's back edge, and that
instruction branches to the same target either way; the run is therefore entry
independent, and this module says so once and for all.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
