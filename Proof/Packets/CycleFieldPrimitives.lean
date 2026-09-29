import Proof.Assembly.AppendFrameKernel
import Proof.Hierarchy.CompetitorRecordRewind
import Proof.MachineModel.Runs

/-! Concrete reusable field operations for the padded physical cycle.
Lengths, zero reserves and unary sweep drivers are explicit tape inputs.
The same machines work at every runtime size, preserve all source bits,
and pay for framing, clearing and head restoration. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace CycleFields.Primitives
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
noncomputable section

abbrev eraseMachine (t : Nat) := RecoveryScratchErase.resetMachine t

def eraseInput {t : Nat} (capacity logCap : Nat) (A : Fin t→List Bool) :
    Fin (t+1+1)→List Bool :=
  Fin.addCases (Fin.addCases A (fun _ : Fin 1=>List.replicate capacity true))
    (fun _ : Fin 1=>List.replicate logCap false)

def eraseOutput (t capacity logCap : Nat) : Fin (t+1+1)→List Bool :=
  eraseInput capacity logCap (fun _ : Fin t=>List.replicate capacity false)

/-- Physically clear a whole fixed block, retaining its allocation and its
unary capacity driver. No logical zero-padding step is used as allocation. -/
theorem erase_step {t : Nat} (capacity logCap : Nat) (A : Fin t→List Bool)
    (hA : ∀ i,(A i).length ≤ capacity) (hlog : capacity+1 ≤ logCap) :
    Step (eraseMachine t) (2*capacity+4) (fun _=>0)
      (eraseInput capacity logCap A) (fun _=>0)
      (eraseOutput t capacity logCap) := by
  have h := Step.of_ready (RecoveryScratchErase.erase_ready capacity logCap A hA)
  rw [max_eq_left hlog] at h
  exact h

end
end CycleFields.Primitives
