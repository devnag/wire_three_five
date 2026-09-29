import Proof.Circuits.FixedScheduleAtomLoop
import Proof.MachineModel.BankAtomContextRegisters
import Proof.MachineModel.BankFramedTargetChains

/-!
# The fixed schedule's diagonal cluster, assembled

The fixed twin of `BankDiagonalBodyClosure`.  `FixedScheduleAtomLoop.fixed_bodyRun_ofPresentation`
consumes eleven named premises; three of them belong to the numeral bank and the
schedule's diagonal.  This module replaces all three by statements from which the
bank has been removed, exactly as the inverse cluster does:

* `FixedAtomTableRuns` — the projection runner's balanced table at the bank's
  frame;
* `FixedCaseOnePointRuns` / `FixedCaseTwoPointRuns` — the two chains at the
  requested point code, the bank frame projected away unconditionally.

## What is generic and is therefore *not* replayed

Every program and every frame lemma on this cluster is schedule free and is
cited from the inverse modules unchanged: `BankFrameLoweringAdapter.inverseFrameAdapterProgram`
and `…Fuel`, `BankAtomShapeCountStage.atomShapeCountProgram`/`…Bits`/`…Fuel` with
`run_atomShapeCountProgram`, `BankAtomContextRegisters.inverseAtomContextProgram`,
`bankShapeNumeralProgram`/`bankShapeNumerals` with `run_bankShapeNumeralProgram`,
`BankAtomContextRegisters.inverseBankWidth`/`inverseBankQueryCount` (both are
functions of the request's *public length* alone, with no schedule in them), and
`BankFramedTargetChains.bankFramedChainProgram`/`bankFramedChainFuel` with
`run_bankFramedChainProgram`.  `BankScheduleDiagonal.sourceIndexOfLength_of_eq_sourceLength`
and `bankSourceLength_of_eq_sourceLength` are index generic and are reused.

## The diagonal on this schedule

`hdiagonal` is still required — the fixed schedule is not length uniform — but
its statement is one function application shorter than the inverse one, because
the fixed chain's index is `CaseOneRecoveryAssembly.fixedSelectedSource` itself
with no `RecoveryScheduleEnvelope.inverseSourceIndex` in front of it.
-/

namespace NearCubicWires.FixedScheduleDiagonalClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The frame-lowering adapter at the fixed bank -/

/-! ## 2. What the atom-shape stage has to compute -/

/-! ## 3. The atom-shape stage from the context half alone -/

/-! ## 4. The context, from the table stage alone -/

/-! ## 5. The two chain premises at the fixed bank, frame free

`BankFramedTargetChains.bankFramedChainProgram` and `run_bankFramedChainProgram`
read no schedule numeral — the point code is four right projections out of the
bank's frame at *every* public length — so only the width envelope is replayed
here. -/

/-! ## 6. The atom-shape stage of the fixed diagonal cluster -/

/-! ## 7. The frame-lowering adapter of the fixed diagonal cluster -/

/-! ## 8. `bodyRun` from the fixed cluster's frame-free residuals -/

end NearCubicWires.FixedScheduleDiagonalClosure
