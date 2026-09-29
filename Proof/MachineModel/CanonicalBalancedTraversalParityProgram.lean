import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalTaggedParityProgram

namespace NearCubicWires.CanonicalBalancedTraversalParityProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTaggedParityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## §1 Parity of a bit list is its sum modulo two

`taggedParity` is the semantic output the substrate's run theorems deliver, so
the repair has to reproduce it exactly.  For a list whose entries are Boolean
codes it is the residue of the plain natural sum, which is what a balanced
summation traversal already computes. -/

/-! ## §2 The low bit of a natural

Three instructions.  `testBit` is a total random-access digit extraction whose
result is always one bit, so its bounded write needs nothing beyond a positive
register width. -/

end NearCubicWires.CanonicalBalancedTraversalParityProgram
