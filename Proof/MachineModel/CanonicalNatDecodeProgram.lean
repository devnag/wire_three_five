import Proof.MachineModel.BalancedClauseStreamFlattenProgram

/-!
# Canonical balanced-bit to native-natural decoder

`encodeNat` stores little-endian bits in the public canonical balanced-list
format.  This module supplies its one executable inverse.  It reuses the
audited balanced traversal and flattening controller: the first pass wraps
each bit as a singleton tagged stream, the existing flatten pass emits one
forward tagged bit stream, and a final fixed arithmetic fold computes the
native natural.  No alternate public encoding or new machine opcode is added.
-/

namespace NearCubicWires.CanonicalNatDecodeProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## Balanced bits to singleton tagged streams -/

/-! The raw canonicality path reasons first about a structural tree and only
later checks midpoint rebalancing.  This corollary exposes the same controller
and leaf handler at that intermediate boundary. -/

/-! ## Reuse the proven balanced stream flattener -/

/-! ## Tagged little-endian bit arithmetic fold -/

/-! ## One public decoder for `encodeNat` -/

end NearCubicWires.CanonicalNatDecodeProgram
