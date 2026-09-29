import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.CanonicalBitSerialModProgram

/-!
# Fixed projected-random-bit evaluation

The public projection table stores an encoded `ProjectedRandomBit`, while the
structural compiler must evaluate that code at a run-time randomness word.
This module implements the total public decoder with one fixed program.  Both
remainders use the bit-serial implementation, so arbitrary imported codes
cannot induce value-linear controller traces.
-/

namespace NearCubicWires.CanonicalProjectedRandomBitProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialModProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/- The canonical remainder program returns zero on divisor zero.  The decoded
projection ignores its index in that case, so normalizing here gives one total
ABI without adding a second arithmetic implementation. -/

/-! ## Public request adapter -/

/-! ## Boolean evaluator after the two canonical remainders -/

/- `bitSerialModProgram` treats a zero divisor as an invalid public request and
returns zero.  Projected-bit decoding deliberately uses that total branch
because the zero-width semantic case ignores the computed index. -/

/-! ## Fixed public entry point -/

/-! ## Polynomial runner package -/

end NearCubicWires.CanonicalProjectedRandomBitProgram
