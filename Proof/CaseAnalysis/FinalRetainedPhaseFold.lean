import Proof.CaseAnalysis.FinalTailComposeUniform
import Proof.CaseAnalysis.FinalWordsStage

/-!
The selected C10 phase consumer: prepare dimensions from the actual completed
stream, fold and emit its estimate, then rewind the same physical run. Fixed
per-phase fresh consumer banks retain one common cold/cache/pool. The two width
outputs and result word are written directly at their final tail ports.

Every source input, stream/count identity, validity premise and exact empty
consumer cell remains explicit. The theorem preserves ambient heads and all
other tapes; in particular the loop counter is outside this focused consumer.
The fuel is exactly the existing words budget, one composition bridge, and the
existing Rewind bound for the existing docked fold. No source/capacity/schedule
or whole-worker Runtime theorem is asserted here.
-/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold
open NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.CloseoutFinal
open RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open CloseoutFinalC10WorkerWidth CloseoutFinalC10WorkerFold
open CloseoutRowsOriginalSchedule
open CloseoutRowsEstimatorCoefficients.Stream
open CloseoutFinalC10WorkerDock CloseoutFinalC10WorkerEmitShape CloseoutFinalC10WorkerDockBody
open CloseoutFinalC10WorkerLoaderPorts CloseoutFinalC10WorkerEmitLoader
open CloseoutFinalC10WordsStage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tailSlots (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) : Fin 475 → Fin B := fun i =>
  ⟨if i.val = 473 then 217 else L+124+i.val, by
    have := i.isLt
    split_ifs <;> omega⟩
def phaseBank (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) : NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → Fin 278 → Fin B := fun ph i =>
    let index := (NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots.phaseIndex ph).val
    if i.val = 0 ∨ i.val = 1 ∨ i.val = 216 ∨ i.val = 217 ∨ index = 0 then
      ⟨i.val, by have := i.isLt; omega⟩
    else
      ⟨L+599+(index-1)*278+i.val, by
        have hi := i.isLt
        have hp := (NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots.phaseIndex ph).isLt
        dsimp only [index] at *
        omega⟩

def wordSlots (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) : NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → Fin 278 → Fin B := fun ph i =>
  if i.val = 274 then tailSlots L B hL hFresh (NearCubicWires.RepairSource.CloseoutFinal.C10TailSlotsUniform.widthSlotT ph 0)
  else if i.val = 275 then tailSlots L B hL hFresh (NearCubicWires.RepairSource.CloseoutFinal.C10TailSlotsUniform.widthSlotT ph 1)
  else phaseBank L B hL hFresh ph i
def foldSlots (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) : NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → Fin 219 → Fin B := fun ph i =>
  if i.val = 215 then tailSlots L B hL hFresh (NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdict.scratchT ph)
  else if i.val = 218 then
    tailSlots L B hL hFresh ⟨8+(NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots.phaseIndex ph).val, by
      have := (NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots.phaseIndex ph).isLt
      omega⟩
  else phaseBank L B hL hFresh ph ⟨i.val, by have := i.isLt; omega⟩


noncomputable def machine (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154<B) (ph : Phase) :=
  Composition.machine (RecoveryFocus.machine (wordSlots L B hL hFresh ph) wordsMachine)
    (RecoveryFocus.machine (foldSlots L B hL hFresh ph)
      (Rewind.machine (CloseoutFinalC10StageSeam.dockedBody emitLoader)))

end NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold
