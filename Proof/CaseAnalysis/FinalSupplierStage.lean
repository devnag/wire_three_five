import Proof.CaseAnalysis.FinalWordsStage
import Proof.CaseAnalysis.FinalStageSeam
import Proof.CaseAnalysis.FinalStageSeamBlock
import Proof.CaseAnalysis.FinalTailCompose

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (DockReady joinScalarWidth flag
  result inputTape)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape (EmitEntry)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold (foldWidth)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other
  install_existing)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The words stage's tapes sit at the bottom of the stage bank -/

/-- The prefix slot map: tape `k` of the words stage is tape `k` of the stage. -/
def wslot (extra : ℕ) (i : Fin (219 + CloseoutFinalC10WordsStage.s)) :
    Fin (218 + (60 + extra)) :=
  ⟨i.val, by
    have h := i.isLt
    have hs : CloseoutFinalC10WordsStage.s = 59 := rfl
    omega⟩

theorem wslot_val (extra : ℕ) (i : Fin (219 + CloseoutFinalC10WordsStage.s)) :
    (wslot extra i).val = i.val := rfl

theorem wslot_inj (extra : ℕ) : Function.Injective (wslot extra) := by
  intro a b hab
  exact Fin.ext (by simpa only [wslot_val] using congrArg Fin.val hab)

/-- A bank port of the dock, as a words-stage port. -/
theorem castAdd_eq_wslot (extra : ℕ) (k : Fin 218)
    (j : Fin (219 + CloseoutFinalC10WordsStage.s)) (h : k.val = j.val) :
    Fin.castAdd (60 + extra) k = wslot extra j := Fin.ext h

/-- An extension port of the stage, as a words-stage port. -/
theorem natAdd_eq_wslot (extra : ℕ) (k : Fin (60 + extra))
    (j : Fin (219 + CloseoutFinalC10WordsStage.s)) (h : 218 + k.val = j.val) :
    Fin.natAdd 218 k = wslot extra j := Fin.ext h

/-- Splitting a stage-bank tape function into the dock's bank and the extension. -/
theorem addCases_restrict {n : ℕ} (T : Fin (218 + n) → List Bool) :
    Fin.addCases (fun k : Fin 218 => T (Fin.castAdd n k))
      (fun k : Fin n => T (Fin.natAdd 218 k)) = T := by
  funext i
  refine Fin.addCases (m := 218) (n := n) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
  · rw [Fin.addCases_right]

/-- Docking a heads profile that is zero inside and zero outside is zero. -/
theorem dockH_zero {t u : ℕ} (slots : Fin t → Fin u) :
    dockH slots (fun _ => 0) (fun _ => 0) = (fun _ : Fin u => (0 : ℕ)) := by
  funext i
  cases h : RecoveryFocus.pick slots i with
  | none => simp [dockH, h]
  | some j => simp [dockH, h]

/-- The words stage's view of the stage bank. -/
def wordsBank (extra : ℕ) (mid : Fin (218 + (60 + extra)) → List Bool) :
    Fin (219 + CloseoutFinalC10WordsStage.s) → List Bool := fun j => mid (wslot extra j)

def CallsReady (extra : ℕ) {cs : ℕ} (calls : Machine (218 + (60 + extra)) cs) (fuel : ℕ)
    (entryWidth callCount : ℕ) (stream input witness : List Bool) : Prop :=
  ∃ mid : Fin (218 + (60 + extra)) → List Bool,
    Step calls fuel (fun _ => 0)
      (C10TailCompose.entryOf (C10TailCompose.wflag (60 + extra)) input witness)
      (fun _ => 0) mid ∧
    wordsBank extra mid 81 = stream ∧
    wordsBank extra mid 90 = CompareMachine.word callCount ∧
    wordsBank extra mid ⟨218, by decide⟩ = List.replicate entryWidth true ∧
    wordsBank extra mid 0 = frame input ∧
    wordsBank extra mid 1 = frame witness ∧
    wordsBank extra mid 216 = [true] ∧
    (∀ j : Fin (219 + CloseoutFinalC10WordsStage.s), 2 ≤ j.val → j.val ≠ 81 → j.val ≠ 90 →
      j.val ≠ 216 → j.val ≠ 218 → wordsBank extra mid j = [])

/-! ## §3 The stage, its fuel, and its state count -/

/-- **The supplier stage**: the call loop, then the words stage docked on the
`278`-tape prefix.  Three fixed machines, one per phase, as `external_in.md`
§0.4(2) freezes; the phase enters only through `calls`. -/
noncomputable def stage (extra : ℕ) {cs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (calls : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine (218 + (60 + extra)) (cs ph))
    (ph : CloseoutRowsOriginalSchedule.Phase) :=
  Composition.machine (calls ph)
    (RecoveryFocus.machine (wslot extra) CloseoutFinalC10WordsStage.wordsMachine)

/-- The state count of a machine, so `StageData.st` can name `stage`'s. -/
def stateCount {t n : ℕ} (_ : Machine t n) : ℕ := n

/-- `StageData.st`. -/
noncomputable def stageStates (extra : ℕ) {cs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (calls : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine (218 + (60 + extra)) (cs ph))
    (ph : CloseoutRowsOriginalSchedule.Phase) : ℕ :=
  stateCount (stage extra calls ph)

def stageFuel (callFuel : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ)
    (entryWidth callCount : ℕ → ℕ) (ph : CloseoutRowsOriginalSchedule.Phase) (n : ℕ) : ℕ :=
  callFuel ph n + 1 + CloseoutFinalC10WordsStage.wordsFuel (entryWidth n) (callCount n)

/-! ## §4 The run -/

/-! ## §5 The block, from the prologue obligation alone -/


-- scan (L.md §7.6) is only safe when no `does not depend on any axioms` line is
-- followed by a `depends on axioms` line.

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage
