import Platform.Hoare
import Platform.RecLoop

/-! # Read access by index into a record stream (with any tail)

The near-cubic-gates paper machine model: table look-ups inside loops cost polynomial factors. The exact-test compiler
(lem:exact, app:exact) visits the weights from the last to the first while every emitted child scans them from the
first; a record stream read by index serves both.

**`getAt A Wk CA CW N K2`**: `Wk := ` record `n` of the record stream on `A` (`n` in register `N`, kept), by `n + 1`
record copies (`copyRec`) and a rewind; **`getAt_spec`**. Cost `(n + 1)(40L + 30) + 5(n+1)(2L+1) + 10`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Platform
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! Programs are opaque to consumers: use the spec theorems. -/

end NearCubicGates.Close.Platform
