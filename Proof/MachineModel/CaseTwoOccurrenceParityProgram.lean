import Proof.CaseAnalysis.CaseTwoOccurrenceEvaluation
import Proof.MachineModel.GeneratedBalancedRangeProgram

/-!
# The masked support parity of one Case-2 occurrence

`CaseTwoOccurrenceEvaluation.parityOn_decodeSupport_eq_maskFold` reduces the
systematic half of one occurrence assignment to the exclusive-or fold of the
masked digit list `supportMaskBits`.  This module executes that fold with the
production controller: canonical range generation, one balanced call per index
to a fixed two-digit mask program, and the shared balanced parity substrate of
`CanonicalTaggedParityProgram`.

No decoded support list, `Finset`, or host parity callback crosses the
executable boundary: the support word returned by the factory's
`supportRunner` is read one digit at a time, in place, by the same program for
every index.
-/

namespace NearCubicWires.CaseTwoOccurrenceParityProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTaggedParityProgram
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The fixed two-digit mask callee -/

/-!
Register ABI of the mask callee:

* `r0`: request tail, then output;
* `r2`: digit index;
* `r3`: mask context;
* `r4`: support word;
* `r5`: occurrence input code;
* `r6`: support digit;
* `r7`: input digit.
-/

/-! ## 2. Dropping the retained range context -/

/-! ## 3. The complete masked parity stage -/

end NearCubicWires.CaseTwoOccurrenceParityProgram
