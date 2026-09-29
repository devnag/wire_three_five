import Proof.CaseAnalysis.CaseTwoOccurrenceEvaluation

/-!
# The four factory runner calls of one Case-2 occurrence

`CaseTwoOccurrenceEvaluation` reduces one honest occurrence value to four
`PolynomialNatProgram.execute` calls on the published factory.  This module
makes each of them an actual interpreter run of the single canonical
native-input caller: the callee is the factory's own program, selected at link
time, and the request is data on the caller's input.

Every theorem below is an exact run at explicitly charged width and fuel, so
the remaining Case-2 evaluator has to route request codes only, never
programs.
-/

namespace NearCubicWires.CaseTwoOccurrenceRunnerCalls

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## 1. Shape -/

/-! ## 2. Systematic support -/

/-! ## 3. Clause -/

/-! ## 4. Honest auxiliary word -/

end NearCubicWires.CaseTwoOccurrenceRunnerCalls
