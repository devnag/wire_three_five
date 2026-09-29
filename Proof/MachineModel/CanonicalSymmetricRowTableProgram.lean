import Proof.MachineModel.CanonicalFourfoldRowProducerDispatchProgram
import Proof.MachineModel.CanonicalSignedGateEvaluationProgram

/-!
# The symmetric row table producer, linked to its front end

`CanonicalSignedGateEvaluationProgram` §10 compiles the residual assignment
table of an arbitrary occurrence pool from one host-shaped input,

```text
    residualAssignmentTableInput occurrences inputMask liveMask
```

and `CanonicalFourfoldRowProducerDispatchProgram` §4 consumes the resulting
context as the `htable` premise of the fork row evaluator.  Between them sits
exactly one front end: the program turning a row-tail handoff into that input.

This module is the seam.  It fixes the linked producer

```text
    symmetricRowTableProgram requestProgram :=
      linkPrograms requestProgram residualAssignmentTableProgram
```

and discharges `htable` from a single interpreter premise on
`requestProgram`, with the greedy live-set selector entering only through the
abstract mask equation `hlive`.  The same premise then instantiates the
symmetric fork row evaluator, so the whole symmetric row evaluator is a fixed
program over exactly two link-time producers with one exact contract each.
-/

namespace NearCubicWires.CanonicalSymmetricRowTableProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalFourfoldRowProducerDispatchProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalFourfoldRowTailProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.CanonicalStructuralGF2EvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 The linked table producer

The front end is a link-time parameter with one exact contract.  Nothing below
inspects it, so the same theorem serves the symmetric family however that
front end is eventually compiled. -/

/-! ## §2 The symmetric fork row evaluator over the front end

Substituting §1 into the dispatcher's row theorem replaces the `htable`
premise by the front end's own contract.  The remaining producer premise is
the polynomial side, stated on every row index through the total row
polynomial of the dispatch module. -/

end NearCubicWires.CanonicalSymmetricRowTableProgram
