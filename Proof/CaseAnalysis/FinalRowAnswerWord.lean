import Proof.CaseAnalysis.FinalAnswerShift
import Proof.CaseAnalysis.FinalExternalRowLoop

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RowAnswerWord

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
  (rowAnswer rowDenominator)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
  (answer seedExponent rowAnswer_le_rowDenominator)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank)
open NearCubicWires.RepairSource.CloseoutFinal.C10ExternalRowLoop
  (pairList pairValue familyTotal_eq_acceptanceCount pairList_length familyWriter familyFuel
    flatten_getD)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
  (widthAt widthPower one_le_widthPower widthPower_le_logScale widthConst thresholdFloor
    entryWidthSchedule partsOnset width_ge_floor)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierWalk

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The payloads of the external-row family, and their total

A.13.9's numerator, as a LIST of per-row counts. -/

/-! ## §2 The summation engine, with its heads parked

`CompetitorCountEntry.machine` (`Proof/Hierarchy/CompetitorCountEntry.lean`) leaves its
source and count cursors where it found the ends of the words
(`CompetitorCountEntry.finalHeads`, `Proof/Hierarchy/CompetitorCountEntryHeads.lean`), so
it is not by itself dock-shaped.  `Rewind.machine`
(`Proof/Foundations/OrdinaryRewind.lean`) adds one workspace tape and parks every head at
`0` for twice the run plus two. -/

/-! ## §4 THE DELIVERABLE: `rowAnswer` on the C.10 band, in binary at width `w`

`round_step_of_dock` (`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) lifts
the docked stage to a `Step` between two round banks.  The conclusion is exactly
the hypothesis `h8` of `answer_shift_bank_dock`
(`Proof/CaseAnalysis/FinalAnswerShift.lean`). -/

/-! ## §5 The word the summation eats is the loop's own emit

`family_run` (`Proof/CaseAnalysis/FinalExternalRowLoop.lean`) states its round
body as the HYPOTHESIS `hrow` and lays the emitted words end to end on the
driver's output slot.  The driver `CloseoutRowsDegreeLoop.loop_run`
(`Proof/CaseAnalysis/RowsDegreeLoop.lean`) is generic in the emitted word, so the
same loop at the PAYLOAD-WORD emit lays down exactly `CompetitorCountFold.raw w`
of the payload list -- §4's `h0` -- at the same `familyFuel` and under the same
class of body hypothesis.  Nothing here discharges that body hypothesis; it
relocates it from `Stream.recordWord` to `binary w`. -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10RowAnswerWord
