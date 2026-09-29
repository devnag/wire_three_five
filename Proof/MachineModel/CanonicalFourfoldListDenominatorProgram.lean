import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalFourfoldRowTailProgram

/-!
# The symmetric list denominator, executed from the typed envelope

Every symmetric row of a fourfold request is indexed by a
`NormalizedOccurrenceListSeed` at the *list denominator*

```text
symmetricListDenominator request (fixedTargetDenominator accuracyExponent q)
  = request.circuits.length * (q ^ accuracyExponent + 1)
```

Both the row evaluator and the row counter need that number as a machine value
computed from the typed envelope alone: the evaluator uses it to select the
seed family, the counter uses it to select the canonical walk length.  This
module supplies the fixed program.

The three arithmetic stages already exist — `fixedTargetDenominatorProgram`
for `q ^ accuracyExponent`, `balancedLengthProgram` for the circuit count, and
`bitSerialMulProgram` for the product — so only the two structural repacks
between them are new.  The accuracy exponent is a link-time constant; the
request ABI still carries no denominator field.
-/

namespace NearCubicWires.CanonicalFourfoldListDenominatorProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 The two structural repacks -/

/-! ## §2 The composed list denominator -/

/-! ## §3 The published symmetric specialization -/

end NearCubicWires.CanonicalFourfoldListDenominatorProgram
