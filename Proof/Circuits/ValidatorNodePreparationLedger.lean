import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorLeafPremiseSweep
import Proof.Circuits.ValidatorTaggedSpineLedger

namespace NearCubicWires.ValidatorNodePreparationLedger

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedListValidationProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorDescriptionLeafClosure
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorTaggedSpineLedger
open NearCubicWires.VerifiedLinker

/-! ## §1 The unit-budget transfer rule

`PolyBounded value (natBitLength raw) budget k` is a statement about one code.
Composed with a certificate for that code's width against the real measure it
becomes a statement about the request family, at `k` times the width's degree.
This is `ValidatorDescriptionLeafClosure` §1 read in the direction the walk
needs. -/

/-! ## §2 The tagged-nat list validator

`taggedNatListValidationFuel` is a six-node `linkFuel` chain over six charges:
the retained spine, the tagged-to-balanced rebuild, the request framing, the
counted call into the canonical natural validator, the singleton tagging and the
stream flattener.  Five are counted by the record's *field count*, which
`ValidatorTaggedSpineLedger` §3 caps by the record's width; the sixth is the
counted call, and it is the only node that raises the degree. -/

end NearCubicWires.ValidatorNodePreparationLedger
