import Proof.CaseAnalysis.FinalAnswerShift
import Proof.CaseAnalysis.FinalExternalRowLoop
import Proof.Hierarchy.CompetitorCountEntry
import Proof.MachineModel.OrdinaryRewindWorkspace

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RowAnswerWord

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
  (rowAnswer rowDenominator)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10AnswerShift
  (rowDenominator_eq_two_pow shiftAmount answerShiftFuel answer_shift_bank_dock)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
  (answer seedExponent rowAnswer_le_rowDenominator)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
  (bank_scratch_apply scratchOf scratchOf_apply round_step_of_dock)
open NearCubicWires.RepairSource.CloseoutFinal.C10ExternalRowLoop
  (pairList pairValue familyTotal_eq_acceptanceCount pairList_length familyWriter familyFuel
    flatten_getD)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
  (widthAt widthPower one_le_widthPower widthPower_le_logScale widthConst thresholdFloor
    entryWidthSchedule partsOnset width_ge_floor)
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
  (polyFuel poly_polylog_le_polyFuel repinOnset partsOnset_le_repinOnset)
open NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable (hotFuel polyFuel_le_hotFuel)
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

/-- **The summation machine**: the corpus's natural-count fold, rewound. -/
noncomputable def sumMachine :
    Machine (9 + 1) (2 + Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control 17) + 2) :=
  Rewind.machine CompetitorCountEntry.machine

/-- **The summation's fuel**: `2 * (rows * (16*w+20) + 5) + 2`.  Linear in the
number of external rows, linear in the record width -- `paper.tex:1382-1385`'s
`q^{O(1)}`, not `paper.tex:3555-3557`'s `2^q/q^\sigma`. -/
def rowAnswerFuel (w rows : ℕ) : ℕ := 2 * (rows * (16 * w + 20) + 5) + 2

/-- The ten tapes the summation reads, at scalar width `w` on both the cell and
the accumulator: the payload stream, the two paid widths, the accumulator seeded
at `frame (binary w 0)`, the field backing, the round counter, and three blanks
plus the rewind workspace. -/
noncomputable def sumInput (w : ℕ) (xs : List ℕ) : Fin (9 + 1) → List Bool :=
  fun i => match i.val with
    | 0 => CompetitorCountFold.raw w xs
    | 1 => List.replicate w true
    | 2 => List.replicate w true
    | 4 => List.replicate (2 * w + 1) false
    | 5 => frame (binary w 0)
    | 8 => RepairSource.VerifierDecoding.CompareMachine.word xs.length
    | _ => []

theorem sumInput_eq (w : ℕ) (xs : List ℕ) :
    (Fin.addCases (motive := fun _ : Fin (9 + 1) => List Bool)
        (CompetitorCountEntry.input w w xs) (fun _ : Fin 1 => List.replicate 0 false))
      = sumInput w xs := by
  funext i
  fin_cases i <;> rfl

theorem sum_ready (w : ℕ) (xs : List ℕ)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hfit : xs.sum < 2 ^ w) :
    ∃ r : ExecutionReceipt (9 + 1)
        (2 + Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control 17) + 2),
      run sumMachine (rowAnswerFuel w xs.length) (sumInput w xs) = some r ∧
      r.final.tapes 5 = frame (binary w xs.sum) ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps ≤ rowAnswerFuel w xs.length := by
  obtain ⟨base, hbase, h5, _h0, hsteps⟩ :=
    CompetitorCountEntry.entry_run w w xs (le_refl w) hx hfit
  obtain ⟨r, hrun, htapes, _hwork, hheads, hrsteps, _⟩ :=
    Rewind.Workspace.reset_workspace CompetitorCountEntry.machine _ _ base hbase 0
  rw [hsteps] at hrun hrsteps
  rw [sumInput_eq w xs] at hrun
  refine ⟨r, hrun, ?_, hheads, le_of_eq hrsteps⟩
  exact (htapes 5).trans h5

/-- **The natural-count summation, docked.**  Slot `0` carries the concatenated
payload words, slots `1` and `2` the paid widths, slot `4` the field backing,
slot `5` the accumulator seeded at zero, slot `8` the round counter; slots `3`,
`6`, `7` and the rewind workspace `9` start blank.  On exit slot `5` carries
`frame (binary w xs.sum)`, every head is parked at `0`, and every tape outside
the slot map is untouched. -/
theorem sum_dock {m : ℕ} (w : ℕ) (xs : List ℕ)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hfit : xs.sum < 2 ^ w)
    (slots : Fin (9 + 1) → Fin m) (hinj : Function.Injective slots)
    (H : Fin m → ℕ) (A : Fin m → List Bool) (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = CompetitorCountFold.raw w xs)
    (h1 : A (slots 1) = List.replicate w true)
    (h2 : A (slots 2) = List.replicate w true)
    (h4 : A (slots 4) = List.replicate (2 * w + 1) false)
    (h5 : A (slots 5) = frame (binary w 0))
    (h8 : A (slots 8) = RepairSource.VerifierDecoding.CompareMachine.word xs.length)
    (hblank : ∀ j : Fin (9 + 1), j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 2 → j.val ≠ 4 → j.val ≠ 5 →
      j.val ≠ 8 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots sumMachine) (rowAnswerFuel w xs.length) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 5) = frame (binary w xs.sum) ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨rc, hrun, ht5, hheads, hsteps⟩ := sum_ready w xs hx hfit
  have hstep : Step sumMachine (rowAnswerFuel w xs.length) (fun _ => 0) (sumInput w xs)
      (fun _ => 0) rc.final.tapes :=
    ⟨rc, hrun, funext hheads, rfl, hsteps⟩
  have hA : ∀ j : Fin (9 + 1), A (slots j) = sumInput w xs j := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact hblank 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact h4
    · exact h5
    · exact hblank 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hblank 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact h8
    · exact hblank 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, CloseoutFinalC10WordEngines.dockH_all_zero slots H hH, ?_, ?_⟩
  · exact (RecoveryRootRound.install_slot slots hinj A rc.final.tapes 5).trans ht5
  · intro i hi
    exact RecoveryRootRound.install_other slots A rc.final.tapes i hi

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
