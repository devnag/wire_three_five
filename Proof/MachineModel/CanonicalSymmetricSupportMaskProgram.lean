import Proof.MachineModel.CanonicalTouchingSweepRoundProgram

/-!
# The symmetric occurrence pool's support masks, executed from the envelope

`CanonicalTouchingSweepRoundProgram` runs the whole greedy sweep on the pool's
`coordinateMask` list, but it receives that list as data.  This module produces
it from the typed request envelope, so the symmetric counting path no longer
assumes any preprocessed input.

Three structural facts make the stage a straight composition of already
compiled pieces.

* The symmetric family's occurrence pool is the concatenation of the circuits'
  bottom fans: `symmetricCircuitOccurrences circuit = List.ofFn circuit.bottom`.
  No retained-index selection happens on this side.
* The bottom fan is the *third* field of the circuit's canonical tagged-list
  encoding, and it is already a balanced list of gate codes.
* One gate's support is the *third* field of its own tagged-list encoding, as a
  canonical `encodeBoolList`.  Since `encodeBoolList` is a balanced list of bit
  codes and `coordinateMask` is the little-endian numeral of the same bits, the
  existing `canonicalNatDecodeProgram` — a balanced-to-tagged flattener followed
  by the tagged little-endian fold — computes the mask exactly.  No counted
  coordinate loop and no power-of-two table are needed.

The remaining work is shape: the outer balanced map produces one balanced mask
list per circuit, while the pool wants a single flat one.  Both directions of
the canonical list conversion are already verified
(`balancedBitsToTaggedProgram`, `taggedToBalancedProgram`), so the flattening is
`BalancedClauseStreamFlattenProgram` between them.
-/

namespace NearCubicWires.CanonicalSymmetricSupportMaskProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalTouchingSweepRoundProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 The third tagged field -/

/-! ## §2 A canonical bit list is its own coordinate mask -/

/-! ## §3 One gate's support mask -/

/-! ## §4 One circuit's support-mask stream -/

/-! ## §5 The pool's support-mask list -/

end NearCubicWires.CanonicalSymmetricSupportMaskProgram
