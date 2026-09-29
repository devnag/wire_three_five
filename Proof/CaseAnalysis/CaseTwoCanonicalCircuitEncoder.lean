import Proof.MachineModel.CaseTwoDescriptionBitPoolProgram

/-!
# The recovered oracle's own code, from its canonical description

`CaseTwoDescriptionBitPoolProgram` emits the recovered oracle's canonical
bounded-circuit description as a balanced list of bits, from the emitter's atom
stream and the coordinate count alone.  What the Case-2 encoder of
`CaseTwoSubstitutedCircuitEncoder` still needs is that description *read back*
as `encodeBooleanCircuit`.

That last step is purely combinatorial: the description is `bound + 1` rows of
`6 + 2 · (n + bound + 1)` thermometer bits, every field of every row is the sum
of its own block, and the row tag selects between a node code, the output
address and a padding sentinel.  No SAT query, no public length and no schedule
enters it.

§1 names that decoder as one program with one run contract — a *closed*
statement about balanced bit lists, with no target, no branch and no oracle in
it.  §2 links the pool onto it through the canonical right-preserving frame and
proves the composite emits the recovered oracle's own circuit code.  Together
with `RuntimeCaseTwoSubstitutedEncodingClosure.inverseScheduledOccurrenceEncoding_ofRequestWord`
this is the whole circuit half of the Case-2 request word.
-/

namespace NearCubicWires.CaseTwoCanonicalCircuitEncoder

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseTwoDescriptionBitPoolProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The grouping decoder as a closed contract -/

/-! ## 2. The encoder -/

end NearCubicWires.CaseTwoCanonicalCircuitEncoder
