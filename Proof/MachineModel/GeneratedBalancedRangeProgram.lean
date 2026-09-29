import Proof.Circuits.CanonicalBalancedTraversal
import Proof.Circuits.RegisterBounds

namespace NearCubicWires.GeneratedBalancedRangeProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds

/-! ## Exact execution ledger

The ledger lists values actually written by the trace.  It is deliberately
structural rather than a `pairIter fuel` bound: sequential work must not be
misreported as additional pairing depth.  The later width theorem therefore
has only the logarithmic continuation depth to discharge. -/

/-! ## Controller chunks -/

/-! ## Recursive exact trace -/

/-! ## Public entry point -/

/-! ## Fuel closure -/

/-! ## Register-width closure -/

end NearCubicWires.GeneratedBalancedRangeProgram
