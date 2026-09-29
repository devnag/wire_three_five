import Batteries.Tactic.OpenPrivate
import Proof.Circuits.AmbientLinkEntry
import Proof.MachineModel.RuntimeCaseTwoDescriptionFrameAdapter
import Proof.Supplier.SelectiveTowerClosure

/-!
# The description pool's atom stream, from the closed compiler tower

`RuntimeCaseTwoDescriptionFrameAdapter.inverseScheduledOccurrenceEncoding_ofAtomStream`
leaves the whole Case-2 encoder standing on one premise,
`InverseDescriptionAtomStreamRuns`: from the requested public length alone, one
fixed stream must emit

> `pair atoms (pair nativeWidth sizeBound)`

where `atoms` is `CaseTwoDescriptionBitPoolProgram.descriptionAtomContext`, i.e.
the **balanced** encoding of the schedule's canonical structural atom list.

This module builds that stream and discharges the premise.

## Balanced, not tagged

The published emitter `StructuralAtomEmitterLoopProgram.structuralAtomEmitterProgram`
returns `encodeTaggedList` of the same atom list, and converting a tagged list
back to a balanced one costs `taggedToBalancedRegisterBitsFor`, whose register
width is bounded below by `2 ^ (list length)`.  The route taken here is the
emitter's *first half*, `structuralAtomRangeProgram`, before the two
point-preserving wrappers and before `balancedToTaggedProgram`: its output is
`encodeBalancedList` of the same list, at the loop's own width.  §1 instantiates
it at an executable projection PCP, exactly as
`StructuralAtomCalleeProgram` instantiates the tagged emitter.

## Where the two numerals come from

They are bank registers.  `inverseFrameWidth` is definitionally
`RecoveryScheduleEnvelope.scheduledWidth` at the chain's own source index and
`inverseFrameBound` is definitionally `BankEmittedAtomLoop.inverseScheduleBound`,
so on the schedule's diagonal both are read off
`BankAtomContextRegisters.bankShapeNumerals`, which
`run_bankShapeNumeralProgram` already computes from the numeral bank's frame with
no premise.  §2 is the three-numeral projection that keeps the width and the size
cap and drops the query count.

## Why the whole cluster reduces here

Every stage between the bank's frame and the atom loop is already published, but
each is stated at a request `⟨target, input⟩`, hence at the point code
`encodeBitInput input`.  The atom stream is entered at the point code `target`
itself.  Every underlying run theorem is already code generic; only
`BankProjectionTableStage.inverseAdapterFrame_ofRegisters` names the request's
code, so §3 restates that join fact and the three stages above it at an arbitrary
retained code.  §4 links the numeral bank in front of the result, discharges the
atom loop's six width budgets against the closed tower of
`SelectiveCountCasesInverse.inverseCompilerRuns_closed`, and closes the bank
cluster at the presentation, the schedule diagonal and the scheduled query
counts.
-/

namespace NearCubicWires.InverseDescriptionAtomStream

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BankScheduledRowStageClosure
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectiveCountCasesInverse
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The balanced atom loop at an executable projection PCP -/

/-! ## 2. The width and the size cap, projected out of the shape numerals -/

/-! ## 3. The bank cluster's stages at an arbitrary retained code -/

/-! ## 4. The atom loop's six width budgets -/

/-! ## 5. The atom stream -/

/-! ## 6. The bank cluster at presentation, diagonal and query counts -/

end NearCubicWires.InverseDescriptionAtomStream
