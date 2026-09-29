import Proof.Circuits.ValidatorCircuitPrepareRebuildLedger
import Proof.MachineModel.CaseTwoOccurrenceProgram

/-!
# The oracle triple from the substituted circuit's encoding alone

The oracle half of `RuntimeCaseTwoBlockOccurrenceProgram.occurrencePacket` is
three numerals: the published factory's clause width at the Case-2 substituted
circuit, that circuit's size, and its encoding.  Only the third is recovered
from the accepting oracle; the other two are *functions of it*, and both
functions are already fixed programs.

* The clause width is one published-runner call.
  `CaseTwoOccurrenceRunnerCalls.run_shapeCallProgram` runs the factory's own
  shape runner on `Nat.pair arity (encodeBooleanCircuit circuit)` — exactly the
  arity the schedule quad already emits beside the encoding — and
  `CaseTwoOccurrenceEvaluation.clauseBits_eq_shapeCode` reads the width out of
  its output by two `unpair`s.
* The size is the encoded node count.
  `CanonicalBooleanCircuitValidationProgram.run_booleanCircuitValidationProgram`
  returns `Nat.pair 1 circuit.nodes.length` on a genuine encoding, and it is
  entered at the circuit's own arity through
  `CanonicalNativeCallProgram.nativeContextCallProgram`.

§1 adds the three straight-line frames, §2 the size stage, and §3 the assembled
stream: from `pair arity (encodeBooleanCircuit circuit)` it emits the whole
oracle triple.  Nothing here mentions the schedule, the recovered oracle, or
any target-derived immediate.
-/

namespace NearCubicWires.RuntimeCaseTwoOracleTripleProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceRunnerCalls
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorCircuitPrepareRebuildLedger
open NearCubicWires.VerifiedLinker

/-! ## 1. The straight-line frames -/

/-! ## 2. The encoded node count -/

/-! ## 3. The assembled oracle triple -/

end NearCubicWires.RuntimeCaseTwoOracleTripleProgram
