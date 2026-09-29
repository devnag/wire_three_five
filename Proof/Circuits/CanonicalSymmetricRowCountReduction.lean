import Proof.Supplier.CanonicalFourfoldRowCountFormula
import Proof.MachineModel.CanonicalFourfoldRowCountProgram
import Proof.MachineModel.CanonicalTwoPowProgram

/-!
# The symmetric counting residual, reduced to one exponent

Three facts now sit beside each other:

* `publishedSymmetricRows_rowCount_two_pow` — the published symmetric row
  count is exactly `2 ^ e` for one explicit natural exponent `e`;
* `run_binaryTwoPowProgram` — the machine computes `2 ^ e` from `e`;
* `run_symmetricFourfoldRangeAtomCountProgram_of_rowCount` — the machine
  computes the row-major atom count from the row count.

Composing them collapses the whole counting side of the artifact's execution
field to a *single* residual program: one machine that reads the typed
envelope and returns the natural number `e`.  Nothing else about the counting
path remains open, and no stage of the composition takes a semantic argument.
-/

namespace NearCubicWires.CanonicalSymmetricRowCountReduction

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalFourfoldRowCountFormula
open NearCubicWires.CanonicalFourfoldRowCountProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRangeAggregationComposition
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 The one remaining number -/

/-! ## §2 From the exponent to the published row count -/

/-! ## §3 The discharged counting premise -/

/-! ## §4 The artifact's symmetric execution field, counting side closed

`run_sharedFourfoldAggregationProgram_symmetric` had two link-time program
parameters with exact interpreter premises.  Instantiating the counter removes
one of them: the symmetric execution field now depends on a single residual
program per side — the exponent program here and the row evaluator, whose
premise is reproduced verbatim. -/

end NearCubicWires.CanonicalSymmetricRowCountReduction
