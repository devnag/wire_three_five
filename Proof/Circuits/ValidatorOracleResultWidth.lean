import Proof.Circuits.ValidatorNodePreparationLedger

/-!
# The oracle stage's result width

`ValidatorLeafPremiseSweep` §4 names `hresult` — the width of
`recoveryOracleValidationResult` — as the width-side twin of the Boolean circuit
validator's fuel charge.  It is not a twin at all: the circuit validator is a
*fail-closed acceptance gate*, so its output is either the closed sentinel `0`
or the single pairing `Nat.pair 1 (booleanCircuitNodeCount inputLength raw)` —
and the node count is exactly the quantity `ValidatorCircuitStageWidths` §2
already capped, at `16` times the code's width, on the way to the comparison
stage's ledger.

So the whole obligation is one four-way case split over the gate's guards and
one pairing step.  No decoded magnitude is read, and nothing below the gate is
needed: the output ledger is strictly cheaper than the fuel ledger it was paired
with.
-/

namespace NearCubicWires.ValidatorOracleResultWidth

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.ValidatorCircuitStageWidths
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination

/-! ## §1 The acceptance gate's only nonzero value -/

/-! ## §2 At the handoff's oracle projection -/

end NearCubicWires.ValidatorOracleResultWidth
