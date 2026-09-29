import Proof.MachineModel.BankFrameLoweringAdapter

/-!
# The atom-shape stage's count half, executed

`BankFrameLoweringAdapter.inverseFrameAdapterRuns_ofShape` leaves exactly one
residual, `InverseAtomShapeRuns`: from the numeral bank's frame produce

`generatedBalancedRangeInput count context`,

and §4 of that module warns that — unlike the context, which is pure pairing —
the count is `tableBoundedOracleStructuralFormulaLength`, which reads the
runner table's *contents* and not only its shape numerals.

## The count is already executed

It is, and by a program this fleet already ships.
`BoundedOracleStructuralSelectiveProgram.structuralFormulaProgram` returns
`structuralFormulaResponseCode = pair length atom` — the formula *length* beside
the atom — and `StructuralAtomCalleeProgram.structuralAtomTakeRightProgram`
throws the length away because the emitter loop wants the atom.  Projecting the
other component instead computes the count, at the same one premise
(`StructuralCompilerRunsAt`) and with no new obligation class: the length
component does not depend on the requested index, so index `0` serves, and
`0 < inverseAtomCount` holds unconditionally because the length is a successor.

§1–§2 build that projection.  §3–§4 assemble the count in front of the context

`context ↦ pair count context = generatedBalancedRangeInput count context`

as one reusable stage.  §5 discharges `InverseAtomShapeRuns` from it: what is
left is `InverseAtomContextRuns`, the *context* half alone — the projection
runner's balanced table paired with the bank's own width, query-count and
size-cap registers, and nothing that reads the table's contents.

## What this does not do

The count premise is `InverseCompilerRuns` at index `0`, i.e. literally the
premise `BankEmittedAtomLoop.inverse_bodyRun_ofCompiler` already carries, so no
hypothesis is added.  The diagonal is untouched: neither §4 nor §5 mentions a
schedule length, so the schedule-diagonal identification remains confined to the
context half, exactly where `BankFrameLoweringAdapter` §4 located it.
-/

namespace NearCubicWires.BankAtomShapeCountStage

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The other response projection -/

/-! ## 2. The compiled formula length, executed -/

/-! ## 3. The request frame of the count stage -/

/-! ## 4. The count installed in front of the context -/

/-! ## 5. `InverseAtomShapeRuns` from the context half alone -/

end NearCubicWires.BankAtomShapeCountStage
