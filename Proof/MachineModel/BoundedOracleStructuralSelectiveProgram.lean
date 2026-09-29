import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.MachineModel.CanonicalProjectedRandomBitProgram
import Proof.MachineModel.CanonicalThreeCNFLiteralProgram
import Proof.Supplier.BoundedOracleStructuralSelectiveCompiler

/-!
# Fixed selective bounded-oracle structural program

This module is the executable boundary for the table-driven structural
compiler.  A request contains exactly one formula index and the public
projection-table context.  The table is converted once from its canonical
balanced representation to the internal tagged traversal spine; no decoded
list, node schedule, formula, certificate, or semantic callback crosses the
machine boundary.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalEncodedListLengthProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalProjectedRandomBitProgram
open NearCubicWires.CanonicalThreeCNFLiteralProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Public-context preparation -/

/-! ## Canonical table preparation -/

/-! ## Native shape and target scheduler -/

/-! ## Single public-to-controller prelude -/

/-! ## Internal tagged-table lookup -/

/-! The scheduler retains live wires in reverse order so every append is one
private cons.  This fixed pass restores forward order only at consumers whose
canonical emission order depends on the original indices. -/

/-! ## Canonical selective-emission microkernel -/

/-! The nested structural compiler has data-dependent loop clocks.  Its
internal runner lemmas therefore carry the concrete interpreter resources they
construct instead of asking callers to predict a separate clock. -/

/-! ## Canonical unary-expression scheduler -/

/-! ## Exact structural-response assembler -/

/-! ## Canonical public structural runner -/

/-! The public linker proof below isolates the one remaining compiler
execution obligation.  Callers consume it with the compiler's own run as a
named premise, and consume the closed runner theorem once the nested compiler
trace discharges that premise. -/

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
