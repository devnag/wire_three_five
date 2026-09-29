import Proof.MachineModel.CanonicalTaggedNatListValidationProgram

/-!
# Canonical Boolean-node validation

Boolean nodes are the first nested witness object whose fields have semantic
relationships.  This module deliberately consumes the one shared tagged-Nat
validation pipeline: no second decoder is allowed to reinterpret public Nat
codes.  The fixed postprocessor below sees only presence-tagged native values
and emits one presence-tagged native node descriptor.
-/

namespace NearCubicWires.CanonicalBooleanNodeValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds
open NearCubicWires.VerifiedLinker

/-!
The postprocessor is private because its input is an internal, trusted ABI.  It
still has a total semantics for every canonical tagged list.  Registers:

* `r0`: tagged cursor, then output;
* `r2`: current presence-tagged field;
* `r3`, `r4`, `r5`: native tag/payload/right values;
* `r6`: tagged-cell payload and pair-construction scratch;
* `r7`: constructor dispatch scratch and the success bit.
-/

/-! ## Structural acceptance characterization -/

end NearCubicWires.CanonicalBooleanNodeValidationProgram
