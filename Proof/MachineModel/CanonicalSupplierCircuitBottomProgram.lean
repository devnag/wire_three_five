import Proof.MachineModel.CanonicalSupplierCircuitHeaderProgram
import Proof.MachineModel.CanonicalSupplierGateBatchProgram

/-!
# Canonical supplier single-circuit bottom decomposition

The native circuit header already contains the decoded bottom count, mode,
balanced bottom-gate tree, and top code.  A fixed adapter moves only the bottom
tree to the left of the pair.  The sole gate-batch program then decomposes that
tree while `preserveRightProgram` retains the remaining circuit context.
-/

namespace NearCubicWires.CanonicalSupplierCircuitBottomProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalSupplierCircuitHeaderProgram
open NearCubicWires.CanonicalSupplierGateBatchProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Fixed native-header adapter -/

/-! ## Header to exact bottom decompositions -/

end NearCubicWires.CanonicalSupplierCircuitBottomProgram
