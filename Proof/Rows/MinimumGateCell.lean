import Proof.Rows.FullGateRun
import Proof.Rows.MinimumMaskReady

/-! One actual residual-constant cell: generate xMin from retained original
native fields, evaluate the unchanged strict gate, append its flag, then clear
xMin. The full bank is reusable and the existing output prefix is never read. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_MinimumGateCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_FullGateBounds PCJ45bee56da9f34d5a_CellGatePalette
open scoped BigOperators
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CellGate.machine

def member {q : Nat} (live : Finset (Fin q)) := List.ofFn (fun i=>decide (i ∈ live))
def minInput {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q) :=
  PCJ45bee56da9f34d5a_MinimumAssignment.input g live x
def extra {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (H : Nat) : Fin 6→List Bool :=
  ![member live,List.ofFn x,List.replicate H false,CompareMachine.word q,List.replicate H true,List.replicate (H+1) false]
def extraHeads : Fin 6→Nat := ![0,0,0,1,0,0]
def heads (out : List Bool) : Fin 114→Nat := Fin.addCases (m:=108) (n:=6) (motive:=fun _=>Nat) (PCJ45bee56da9f34d5a_CellGatePalette.heads out 0) extraHeads

def slots : Fin 8→Fin 114 := ![0,110,108,109,1,111,112,113]
theorem slots_injective : Function.Injective slots := by decide
def eraseSlots : Fin 3→Fin 114 := ![1,112,113]
def produce := RecoveryFocus.machine slots PCJ45bee56da9f34d5a_MinimumMaskReady.machine
def evaluate := TapeEmbedding.machine 6 PCJ45bee56da9f34d5a_CellGate.machine
def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
def machine := Composition.machine (Composition.machine produce evaluate) erase

end
end PCJ45bee56da9f34d5a_MinimumGateCell
