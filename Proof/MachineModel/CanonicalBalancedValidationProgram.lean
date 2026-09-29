import Proof.Circuits.CanonicalBalancedBuilder
import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.MachineModel.CanonicalNativeEqualityProgram

/-!
# Executable canonical-balanced validation

The validator normalizes one structural balanced tree with the existing
traversal, stream flattener, and midpoint builder, then compares that unique
normal form with the original code.  The public input is only the candidate
code: duplication, preservation, and equality requests are fixed machine
plumbing rather than caller-supplied evidence.
-/

namespace NearCubicWires.CanonicalBalancedValidationProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Total raw syntax normalization -/

/-! ## One canonicalizer assembled from the shared sequence machinery -/

/-! The raw front door is linked exactly once before canonical midpoint
rebuilding.  No downstream consumer may bypass this normalization seam. -/

/-! ## Retain the untrusted code for the final equality guard -/

/-! ## Public Boolean canonicality result -/

end NearCubicWires.CanonicalBalancedValidationProgram
