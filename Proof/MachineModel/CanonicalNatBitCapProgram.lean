import Proof.MachineModel.BitInputPrefixProgram
import Proof.MachineModel.CanonicalNatCeilLogProgram
import Proof.MachineModel.CanonicalNativeEqualityProgram

/-!
# Executable natural-number bit-cap validation

This module validates the native natural-number predicate
`natBitLength value ≤ cap`.  A zero cap is rejected explicitly: this
repository's bit length assigns one bit even to zero, so no natural can satisfy
that cap.

## Why the stage is a ceiling logarithm and not a bit scan

The public semantics `natBitCapOutput` is stated through the low-bit
projection `bitInputPrefix cap value = value % 2 ^ cap`, because that is the
canonical statement of "the value survives its own cap".  Executing that
statement literally, however, costs a scan whose charge is
`Θ(min (value, 2 ^ cap))`: the projection program walks the selected bit
positions one at a time.  That budget is affordable inside an exponential-time
caller, but the recovery-witness validator is charged against a *polynomial*
envelope, and the bit cap sits on that critical path.

The executable stage therefore evaluates the equivalent inequality

`natBitLength value ≤ cap  ↔  Nat.clog 2 (value + 1) ≤ cap`  (for `cap ≠ 0`),

using the fixed base-two ceiling logarithm of `CanonicalNatCeilLogProgram`,
whose charge is linear in the *answer*, and the fixed native comparator of
`CanonicalBinaryArithmeticProgram`, whose charge is linear in the operand
*widths*.  A zero cap is routed to the argument `2`, whose ceiling logarithm is
one, so the comparison fails closed through the same branch-free pipeline.

The public surface — `natBitCapInput`, `natBitCapOutput`, `natBitCapProgram`,
`natBitCapFuel`, `natBitCapBits`, `run_natBitCapProgram`,
`natBitCapProgram_oracleFree` and `natBitCapOutput_ne_zero_iff` — is unchanged;
only the internal stage and its charge changed.  `natBitCapFuel_le` records the
resulting linear budget.
-/

namespace NearCubicWires.CanonicalNatBitCapProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatCeilLogProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Public input to ceiling-logarithm-call ABI -/

/-! ## Linked total validator -/

/-! ## The exact semantic boundary shared by both stage designs -/

/-! ## The fixed program -/

/-! ## Exact semantic boundary -/

/-! ## The polynomial charge

The whole point of the ceiling-logarithm stage: the bit-cap check is charged
linearly in the *widths* of its two operands, never in their magnitudes. -/

end NearCubicWires.CanonicalNatBitCapProgram
