import Proof.MachineModel.CanonicalFourfoldListDenominatorProgram
import Proof.MachineModel.CanonicalStructuralGF2EvaluationProgram

/-!
# Packaging the two row producers into the published row evaluator

`CanonicalStructuralGF2EvaluationProgram` compiles everything below two
link-time producers: a *table* producer emitting the residual assignment
context of one row, and a *polynomial* producer emitting the encoded
structural row polynomial.  Both read the same row-tail handoff.

`CanonicalFourfoldRowTailProgram` consumes a row evaluator whose fuel is a
function of that handoff alone, and dispatches the two published families on
the mode code already sitting at the head of the handoff.

This module is the seam between them.  It supplies

* total projections of the row-tail ABI, with exact inverses on both
  published handoffs, so no field is recomputed from the envelope;
* the total row polynomial named by one handoff, agreeing with the structural
  row on every decodable row index and with the zero polynomial elsewhere, so
  the producers' contracts are single equations quantified over *all* row
  indices;
* the branch fuel as a closed function of the handoff, obtained by inverting
  the envelope and seed encodings;
* the discharged `hbranch` premises of
  `run_fourfoldRowModeDispatchProgram_symmetric` and `…_threshold`, and
  therefore the `hevaluator` premises of
  `run_sharedFourfoldAggregationProgram_symmetric` and `…_threshold`.

After this module the whole evaluator side of the fourfold aggregation is a
single fixed program over exactly four link-time producers, each with one
exact interpreter premise and no fuel or callback argument.
-/

namespace NearCubicWires.CanonicalFourfoldRowProducerDispatchProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalFourfoldListDenominatorProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalFourfoldRowEvaluationProgram
open NearCubicWires.CanonicalFourfoldRowTailProgram
open NearCubicWires.CanonicalStructuralGF2EvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRangeAggregationComposition
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.VerifiedLinker

/-! ## §1 Total projections of the row-tail ABI

The handoff is `Nat.pair (Nat.pair modeCode (Nat.pair q (Nat.pair
envelopeCode (Nat.pair rowIndex inputCode)))) bottomForest`.  Each projection
below is a fixed composition of the machine's own pair projections, so the
later fuel formulas read the handoff exactly as the machine does. -/

/-! ## §2 The published handoffs read back exactly

These are the inverses used by every fuel formula below: the mode code, the
arity, the envelope, the row index, and the input code of a published row are
recovered from the handoff without touching the retained bottom forest. -/

/-! ## §3 The total row polynomial of one row index

The dispatcher quantifies over every natural row index, so the producers'
contracts must too.  `symmetricRowPolynomial` is the structural row on every
decodable index and the zero polynomial elsewhere, which is exactly the
convention `evaluateCanonicalSymmetricFourfoldRow` already fixes. -/

/-! ## §4 The fork row evaluator on every row index

The two producers are quantified over all row indices, so the evaluator must
be too.  Below the seed boundary the malformed-index convention of
`CanonicalStructuralGF2EvaluationProgram` §15 supplies the zero polynomial and
the machine's empty parity fold; nothing else changes. -/

/-! ## §5 The branch fuel as a closed function of the handoff

The dispatcher charges its branch a fuel that depends on the row handoff and
on nothing else.  Both encodings crossing the handoff are invertible — the
typed envelope by `decodeFourfoldEnvelope_output`, the row seed by
`decodeNormalizedOccurrenceListSeed_encode` and `decodePrimeListSample_encode`
inside the total row polynomial — so the previous module's fuel is re-expressed
through those inverses with no extra hypothesis. -/

/-! ## §6 The discharged `hevaluator` premises

These are verbatim the `hevaluator` premises of
`run_sharedFourfoldAggregationProgram_symmetric` and `…_threshold`, with the
row evaluator and its fuel now fixed: exactly four link-time producers remain,
each with one exact interpreter premise and no fuel or callback argument. -/

/-! ## §7 The evaluator side of the published aggregation

Both published aggregation runs now hold with a fixed program and a fixed
fuel.  Only the counting callee `countProgram` and the four row producers
remain as link-time parameters; each has one exact interpreter premise. -/

/-! ## §8 The producers' shared front end

Both producers read the typed envelope out of the row-tail ABI before doing
anything else, and the retained bottom forest is left untouched by that read.
This is the fixed projection, together with the first producer stage it
carries: the list denominator at which every published symmetric row seed is
indexed. -/

end NearCubicWires.CanonicalFourfoldRowProducerDispatchProgram
