import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.MachineModel.GeneratedBalancedRangeProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Canonical supplier support compression

Supplier gates carry parallel canonical balanced vectors of integer weights and
Boolean support bits.  Compression must retain only supported weights without
ever materializing a linear tagged list: such a spine has exponential register
width.  This module starts the production path with a direct balanced-tree
support count.  Its work stack contains only pending balanced subtrees and
therefore has logarithmic depth on canonical inputs.
-/

namespace NearCubicWires.CanonicalSupplierSupportCompressionProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RegisterBounds
open NearCubicWires.VerifiedLinker

/-! ## Semantic support order -/

/-! ## Balanced support count and range-context preparation -/

/-! ## Reusable balanced Boolean aggregation -/

/-! ## Generic nonzero aggregation

Validation callees use zero as their unique rejection result and a nonzero
payload on success.  The Boolean counter above already implements exactly the
required register semantics, so the following theorem exposes that same
program over arbitrary canonical balanced atoms.  This avoids a second
list-fold implementation for each validator family. -/

/-! ## Canonical rank selector -/

/-! ## Fixed support-compression pipeline -/

end NearCubicWires.CanonicalSupplierSupportCompressionProgram
