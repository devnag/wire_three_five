import Proof.Circuits.CanonicalDescriptionGroupingDecoder
import Proof.MachineModel.RuntimeCaseTwoCircuitEncodingClosure

/-!
# The description frame at the scheduled branch

`RuntimeCaseTwoCircuitEncodingClosure.InverseDescriptionFrameRuns` asks for one
stage that, from the requested public length alone, emits the description
pool's own request word

> `pair (generatedBalancedRangeInput descriptionWidth atomStream)
>   (pair nativeWidth sizeBound)`.

Three things are bundled there, and this module separates them.

* **The description width.**  `descriptionWidth W B = (B + 1) · (6 + 2 · (W + B
  + 1))` is pure arithmetic over the two numerals, and *nothing in the tree
  emits it*: there is no `descriptionWidthProgram` anywhere.  §1--§2 build it —
  two straight-line stages around the published bit-serial multiplier — and §3
  discharges that half outright.
* **The two numerals.**  They are not computed here: the adapter keeps them
  verbatim from the stage below it.  This is deliberate.  Both are already
  components of the atom loop's own public request context
  (`BoundedOracleStructuralFormulaTable.tableBoundedOracleStructuralFormulaContext`
  pairs the native width second and the size bound fourth), so a stage that has
  produced the atom stream at a target has produced the numerals with it.
* **The atom stream.**  `descriptionAtomContext` is
  `encodeBalancedList (boundedOracleStructuralFormulaAtoms …)`.  No run contract
  in the tree has that as its output: the published route is
  `StructuralAtomEmitterLoopProgram.structuralAtomRangeProgram` — the *first*
  half of the bank-framed emitter, before its `balancedToTaggedProgram`
  retagging — under `StructuralAtomCalleeProgram.structuralAtomRequests_map`,
  and that stage stands on `BankEmittedAtomLoop.InverseCompilerRuns` exactly as
  the selector side does.  The retagged emitter is *not* an alternative: its
  output is `encodeTaggedList`, and converting back costs
  `taggedToBalancedRegisterBitsFor`, whose register width is bounded below by
  `2 ^ (list length)`
  (`ValidatorTaggedIntermediateVerdict.two_pow_length_le_taggedToBalancedRegisterBitsFor`).

So the atom stream enters here as one named premise, in the same shape the
emitter chain already uses, and §3 shows it is the *only* thing the description
frame still needs.
-/

namespace NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.CaseTwoDescriptionBitPoolProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalDescriptionGroupingDecoder
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoRequestWordFrame
open NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The description width, from the two numerals -/

/-! ## 2. The width stage -/

/-! ## 3. The description frame, from the atom stream alone -/

/-! ## 4. The cluster's encoder premise, from the atom stream alone -/

end NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
