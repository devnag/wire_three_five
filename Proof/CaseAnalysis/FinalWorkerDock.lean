import Proof.CaseAnalysis.FinalSupplierCalls
import Proof.MachineModel.Layout

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The bank -/

/-- The multiply stage's ninety tapes. -/
def entrySlot (j : Fin 90) : Fin 218 := ⟨2 + j.val, by omega⟩

/-- The fold's source tape, as an index of its own bank. -/
def foldSource : Fin 95 := (⟨88, by omega⟩ : Fin 94).castAdd 1

/-- The fold's ninety-five tapes.  Its source tape is the multiply stage's
output port; every other tape is fresh. -/
def foldSlot (j : Fin 95) : Fin 218 :=
  if j.val = 88 then ⟨76, by omega⟩ else ⟨92 + j.val, by omega⟩

/-- The answer emitter's twenty-nine tapes. -/
def answerSlot (j : Fin 29) : Fin 218 := ⟨187 + j.val, by omega⟩

/-- The phase output port: the emitter's own output tape. -/
def port : Fin 218 := answerSlot 28

/-- The gate's scratch slot. -/
def flag : Fin 218 := ⟨216, by omega⟩

/-- The gate's verdict slot. -/
def result : Fin 218 := ⟨217, by omega⟩

/-- The verifier's framed input tape. -/
def inputTape : Fin 218 := ⟨0, by omega⟩

theorem entrySlot_val (j : Fin 90) : (entrySlot j).val = 2 + j.val := rfl

theorem foldSlot_val (j : Fin 95) :
    (foldSlot j).val = if j.val = 88 then 76 else 92 + j.val := by
  unfold foldSlot
  split <;> rfl

theorem entrySlot_injective : Function.Injective entrySlot := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [entrySlot_val, entrySlot_val] at hv
  exact Fin.ext (by omega)

theorem foldSlot_injective : Function.Injective foldSlot := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [foldSlot_val, foldSlot_val] at hv
  have ha := a.isLt
  have hb := b.isLt
  refine Fin.ext ?_
  by_cases hA : a.val = 88
  · by_cases hB : b.val = 88
    · omega
    · rw [if_pos hA, if_neg hB] at hv; omega
  · by_cases hB : b.val = 88
    · rw [if_neg hA, if_pos hB] at hv; omega
    · rw [if_neg hA, if_neg hB] at hv; omega

/-- **The handoff, as a slot identity.**  The fold's source tape IS the
multiply stage's output port `74`.  Nothing is copied between the stages. -/
theorem foldSlot_source : foldSlot foldSource = entrySlot 74 := by
  apply Fin.ext
  rw [foldSlot_val, entrySlot_val]
  rfl

/-- Every other fold tape is fresh: no multiply-stage tape lands on it. -/
theorem entrySlot_ne_foldSlot (j : Fin 95) (hj : j.val ≠ 88) (k : Fin 90) :
    entrySlot k ≠ foldSlot j := by
  intro h
  have hv := congrArg Fin.val h
  rw [entrySlot_val, foldSlot_val, if_neg hj] at hv
  have := k.isLt
  omega

/-! ## §2 The scalar width and the budget -/

/-- The scalar width at which the two stages agree, as a function of the
record width and the NUMBER OF CALLS.  This is `WorkerJoin.joinWidth`, keyed
by the call count rather than by the list. -/
def joinScalarWidth (entryWidth callCount : ℕ) : ℕ :=
  CompetitorSumWidth.width callCount (CompetitorRationalDecision.width entryWidth)

theorem joinScalarWidth_eq (entryWidth : ℕ) (entries : List Entry) :
    joinScalarWidth entryWidth entries.length = joinWidth entryWidth entries := by
  unfold joinScalarWidth joinWidth foldWidth
  rw [contributions_length]

/-- **The body's budget depends on the call count, never on the witness.**
Both summands are the corpus's own stage budgets at the join width; the join
width is a function of the record width and the call count. -/
def dockBudget (entryWidth callCount : ℕ) : ℕ :=
  CompetitorMonomialEntry.readyBudget (joinScalarWidth entryWidth callCount) callCount + 1 +
    CompetitorSumEntry.budget (joinScalarWidth entryWidth callCount) callCount

/-! ## §3 The docked body -/

/-- **The estimator body: one machine on one bank.**  The multiply stage and
the cold fold, each docked by its own slot map, composed by
`Composition.machine`. -/
noncomputable def dockBody :=
  Composition.machine
    (RecoveryFocus.machine entrySlot CompetitorMonomialEntry.machine)
    (RecoveryFocus.machine foldSlot CompetitorSumEntry.machine)

/-- **The bank the body starts from.**  Each stage's own input, at its own
slots -- except the fold's source tape, which the multiply stage produces and
which therefore does NOT appear here.  Every condition is a port projection. -/
structure DockReady (entryWidth : ℕ) (entries : List Entry)
    (bank : Fin 218 → List Bool) : Prop where
  /-- The multiply stage's input, including S1's call-record stream. -/
  multiply : ∀ j : Fin 90,
    bank (entrySlot j) =
      CloseoutRowsEstimatorCoefficients.EntryMachine.readyInput entryWidth
        (joinScalarWidth entryWidth entries.length) entries j
  /-- The fold's input, except its source tape. -/
  fold : ∀ j : Fin 95, j.val ≠ 88 →
    bank (foldSlot j) =
      CompetitorSumEntry.input (joinScalarWidth entryWidth entries.length)
        (contributions entries) j

theorem foldInput_castAdd (scalarWidth : ℕ)
    (terms : List CompetitorValidity.Estimate) (i : Fin 94) :
    CompetitorSumEntry.input scalarWidth terms (i.castAdd 1) =
      CompetitorSumFold.coldInput scalarWidth
        (CompetitorSumFold.words scalarWidth terms) i := by
  simp [CompetitorSumEntry.input, CompetitorSumEntry.extendTapes]

/-- The fold's source tape carries the term stream. -/
theorem foldInput_source (scalarWidth : ℕ)
    (terms : List CompetitorValidity.Estimate) :
    CompetitorSumEntry.input scalarWidth terms foldSource =
      CompetitorSumFold.words scalarWidth terms := by
  rw [foldSource, foldInput_castAdd]
  rfl

/-! ## §4 The docked chain -/

/-! ## §5 The gate front -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
