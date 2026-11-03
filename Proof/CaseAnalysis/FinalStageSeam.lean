import Proof.CaseAnalysis.FinalWorkerEmitBody
import Proof.CaseAnalysis.FinalWorkerDockSeam

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerWidth
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The dock without its loader -/

/-- The dock without its loader. -/
noncomputable def dockedBody {emitStates : ℕ} (emitLoader : Machine 218 emitStates) :=
  Composition.machine dockBody
    (Composition.machine emitLoader
      (RecoveryFocus.machine answerSlot CompetitorCountRecordAppend.machine))

/-- The docked body's fuel: `fullBodyFuel` without the loader's summand. -/
def dockedFuel (emitFuel : ℕ → ℕ) (entryWidth callCount : ℕ) : ℕ → ℕ :=
  fun n => dockBudget entryWidth callCount + 1 +
    (emitFuel n + 1 + CompetitorCountRecordAppend.budget (joinScalarWidth entryWidth callCount))

/-- **`body_runs_of_loader` minus the loader: from any ready bank at heads 0.**
The proof is `(hdock).seq (hemitStep.seq hanswer)` exactly as in
`body_runs_of_loader`, without the leading `hloader.seq`. -/
theorem docked_run (entryWidth : ℕ) (entries : List Entry)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (bank : Fin 218 → List Bool) (hready : DockReady entryWidth entries bank)
    (hentry : EmitEntry (joinScalarWidth entryWidth entries.length) bank) (n : ℕ) :
    ∃ (heads : Fin 218 → ℕ) (exit : Fin 218 → List Bool),
      Step (dockedBody emitLoader)
        (dockedFuel (fun _ => emitFuel (joinScalarWidth entryWidth entries.length))
          entryWidth entries.length n)
        (fun _ => 0) bank heads exit ∧
      exit port = CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (foldWidth (CompetitorRationalDecision.width entryWidth) entries)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)) 1 1 := by
  obtain ⟨dockHeads, dockExit, hdock, hstore, hzero, hanswerPorts⟩ :=
    dock_exit entryWidth entries bank hentries hready
  have hvalid : CompetitorValidity.Estimate.Valid
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
      (joinScalarWidth entryWidth entries.length) := by
    rw [joinScalarWidth_eq entryWidth entries]
    exact answer_valid (CompetitorRationalDecision.width entryWidth)
      entries (contributions_valid entryWidth entries hentries)
  have hexitEntry : EmitEntry (joinScalarWidth entryWidth entries.length) dockExit := by
    intro j
    rw [hanswerPorts j]
    exact hentry j
  obtain ⟨operandHeads, operands, hemitStep, hoperandHeads, hoperands⟩ :=
    emit_loader_step (joinScalarWidth entryWidth entries.length)
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
      (CompetitorSumFold.words (joinScalarWidth entryWidth entries.length)
        (contributions entries))
      dockHeads dockExit hstore hvalid hzero hexitEntry
  obtain ⟨answerHeads, answerExit, hanswer, hencoded⟩ :=
    answer_step (joinScalarWidth entryWidth entries.length)
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
      operandHeads operands hoperandHeads hoperands
  have hwidth : joinScalarWidth entryWidth entries.length =
      foldWidth (CompetitorRationalDecision.width entryWidth) entries :=
    joinScalarWidth_eq entryWidth entries
  rw [hwidth] at hencoded
  exact ⟨answerHeads, answerExit, hdock.seq (hemitStep.seq hanswer), hencoded⟩

/-! ## §2 The layout on `218 + e` tapes -/

/-! ## §3 The stage seam -/

/-- The stage seam: a supplier stage on `218+e` tapes followed by the embedded dock. -/
noncomputable def stagedBody {e st emitStates : ℕ} (stage : Machine (218+e) st)
    (emitLoader : Machine 218 emitStates) :=
  Composition.machine stage (TapeEmbedding.machine e (dockedBody emitLoader))

/-- The seam's fuel: the stage's, one paid bridge step, the docked body's. -/
def stagedFuel (stageFuel emitFuel : ℕ → ℕ) (entryWidth callCount : ℕ) : ℕ → ℕ :=
  fun n => stageFuel n + 1 + dockedFuel emitFuel entryWidth callCount n

end NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam
