import Proof.MachineModel.CanonicalBinaryArithmeticProgram
import Proof.Circuits.CanonicalPairedCall

/-!
# Canonical native-natural equality

Equality reuses the single binary-width comparator in both directions.  The
paired-call adapter retains both requests without another arithmetic loop, and
one fixed gate conjoins the two Boolean results.
-/

namespace NearCubicWires.CanonicalNativeEqualityProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## Public pair request to the symmetric comparator -/

end NearCubicWires.CanonicalNativeEqualityProgram
