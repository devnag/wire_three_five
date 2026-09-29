import Proof.MachineModel.CanonicalOccurrenceRequestProgram
import Proof.MachineModel.CanonicalSymmetricLiveMaskProgram

namespace NearCubicWires.CanonicalSymmetricRowTableRequestProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalFourfoldRowCountFormula
open NearCubicWires.CanonicalFourfoldRowEvaluationProgram
open NearCubicWires.CanonicalFourfoldRowProducerDispatchProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalFourfoldRowTailProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalOccurrenceRequestProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalSignedAtomRequestProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.CanonicalSymmetricLiveMaskProgram
open NearCubicWires.CanonicalSymmetricRowTableProgram
open NearCubicWires.CanonicalStructuralGF2EvaluationProgram
open NearCubicWires.CanonicalSymmetricSupportMaskProgram
open NearCubicWires.CanonicalTouchingSweepRoundProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 The pool's balanced gate tree

The circuit's bottom fan is already a balanced list of encoded gates — the
third field of its canonical tagged encoding — so one circuit's contribution to
the pool needs no decoding at all, only the canonical balanced-to-tagged
conversion that makes it concatenable.  Concatenating and rebalancing once is
then the same three-program tail
`CanonicalSymmetricSupportMaskProgram` uses. -/

/-! ## §4 The row-tail front end's four frames

Three of the pool's inputs are produced from the typed envelope and one is the
handoff's own fifth field, so the front end reads the envelope once, keeps a
copy for each envelope-driven producer, and rotates the accumulated results
into the traversal's request.  All four stages are straight-line pair surgery;
nothing below decodes a circuit. -/

/-! ## §5 The symmetric row's table request

Eight linked stages: the handoff frame, the three envelope-driven producers
with a rotation after each, and the pool traversal under one
`preserveRightProgram` that pairs the population back on.  The result is
exactly `CanonicalSignedGateEvaluationProgram` §10's input. -/

/-! ## §6 The symmetric row evaluator over its compiled front end

§5 is exactly the `hrequest` premise both consumers carry, so instantiating
them at `symmetricRowTableRequestProgram` leaves the symmetric row evaluator
with the polynomial producer as its only interpreter premise. -/

end NearCubicWires.CanonicalSymmetricRowTableRequestProgram
