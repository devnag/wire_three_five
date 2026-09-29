import Proof.MachineModel.BankRefuterWordFrameProgram
import Proof.MachineModel.BoundedOracleStructuralFormulaPrefixSATProgram

/-!
# The branch query, assembled by the machine

`CanonicalBranchSelectorProgram.branchSelectorProgram` decides the scheduled
Case-1/Case-2 split with one `sat` opcode, but it bakes the queried word

`boundedOracleRecoveryCode (paddedOuterPCP outer) word
  (oracleSizeBound requiredDegree width)`

as an immediate of a `set` instruction.  That is the fifth — and last —
target-derived immediate of the two chains: the numeral bank of
`RuntimeScheduleNumeralBank` supplies the other four from registers.

This module removes it.  `boundedOracleRecoveryCode` is by definition

`Encodable.encode (circuitInputFormula (boundedOracleVerifierCircuit pcp word
bound))`,

and every stage of that encoding is already an audited fixed program:

* `CanonicalBalancedBuilder.taggedToBalancedProgram` turns the emitter's tagged
  atom stream into the canonical balanced list;
* `CircuitInputClauseBalancedCall.circuitInputFormulaBalancedFoldProgram` turns
  that list into the forward raw-clause stream of the circuit-input CNF;
* `StructuralClauseStreamProgram.structuralClauseStreamProgram` canonicalizes
  and reverses it;
* `DynamicCNFBuilder.cnfListBuilderProgram` folds the reversed stream into the
  formula's own `Encodable.encode`.

§2--§4 link the four into one oracle-free stream and prove it returns the
recovery code exactly.  §5 wraps it with the `sat` opcode and the retained
point code, so the resulting selector has the same interface as
`branchSelectorProgram` with *no* query immediate, and §6 instantiates it at
the scheduled split, reproducing
`CanonicalBranchSelectorProgram.run_scheduledSelectorProgram_caseOne` and its
Case-2 twin verbatim.

## The one remaining premise

The chain starts at the *tagged atom stream*
`encodeTaggedList (boundedOracleStructuralFormulaAtoms pcp word bound)`.
Producing that stream from the refuter word and the size bound is the
table-driven structural emitter of `BoundedOracleStructuralSelectiveProgram`,
whose pointwise callee still carries its own compiler-run premise; it is
therefore taken here as one named program parameter `emitter` with one named
run hypothesis, and nothing else in the branch query is left open.

§7 supplies the size bound itself from the numeral bank's width register:
`oracleSizeBound requiredDegree` is `pairClock (oracleDepth requiredDegree)`,
and `RuntimeScheduleNumeralBank.pairIterProgram` is that clock as a fixed
stream, so the emitter's second argument is a register read as well.
-/

namespace NearCubicWires.BankRecoveryCodeProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBranchSelectorProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.CircuitInputCNF
open NearCubicWires.DynamicCNFBuilder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The reversed canonical stream folds to the formula's own code

`DynamicCNFBuilder.run_cnfListBuilder` fixes the public input length to
`cnfVariableCount`, which a linked stage cannot choose.  The same
`run_cnfListBuilder_from` refinement holds at every public length. -/

/-! ## 2. From the forward raw-clause stream to the formula code -/

/-! ## 3. From the balanced clause atoms to the formula code -/

/-! ## 4. From the tagged emitter stream to the bounded-oracle recovery code -/

/-! ## 5. The branch selector with no query immediate

`CanonicalBranchSelectorProgram.branchSelectorProgram` is `copy`, `set`, `sat`,
`pair`.  Replacing its `set` by the assembler of §4 keeps the interface — a
retained point code in, the tagged point code out — and removes the immediate.
-/

/-! ## 6. The emitter as the sole remaining parameter -/

/-! ## 7. The scheduled split, decided without an immediate

`CanonicalBranchSelectorProgram.scheduledSelectorQuery` is definitionally the
recovery code of §4 at the scheduled size bound, so the two tag lemmas of that
module apply to the emitted selector unchanged.
-/

end NearCubicWires.BankRecoveryCodeProgram
