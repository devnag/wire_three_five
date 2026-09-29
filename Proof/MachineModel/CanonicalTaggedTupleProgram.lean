import Proof.MachineModel.CanonicalTaggedListValidationProgram
import Proof.Circuits.RegisterBounds

/-!
# Fixed-arity canonical tagged tuples

All fixed records in the recovery witness use the same tagged-list codec.  This
module deconstructs exactly `arity` canonical cells in one pass and returns the
fields in a private reverse-pair accumulator.  The arity is an immediate in
the program text, never caller data; malformed tags, short/long lists, and
nonzero terminators all reach the single zero result.
-/

namespace NearCubicWires.CanonicalTaggedTupleProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds

/-! ## Fixed tuple deconstructor -/

end NearCubicWires.CanonicalTaggedTupleProgram
