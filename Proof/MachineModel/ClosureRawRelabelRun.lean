import Proof.CaseAnalysis.FinalSupplierRowInput
import Proof.MachineModel.ClosureRawRelabelOffset

/-! Reusable physical C10 raw-row construction from the actual lowered stream.
Runtime N and yi are retained unary counters. Offset scratch starts and ends
all zero; source and every control head return to zero. The output append is
the only changing state, and the exact indexRow consumer is proved below. -/
namespace NearCubicWires.P1Closure.RawRelabelRun
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch RecoveryRootRound
open ExtIncidence
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable section

def offsetSlots : Fin 4→Fin 8 := ![1,2,3,5]
def scanSlots : Fin 4→Fin 8 := ![0,3,4,5]
def eraseSlots : Fin 3→Fin 8 := ![3,6,7]
noncomputable def offsetMachine:=RecoveryFocus.machine offsetSlots RawRelabelOffset.machine
noncomputable def scanMachine:=RecoveryFocus.machine scanSlots
  (MaskedReset.machine RawRelabelMachine.machine (fun i=>decide (i=0)))
noncomputable def eraseMachine:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
def move (up : Bool) : Machine 8 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    fun i=>if i=3 then (if up then .right else .left) else .stay⟩ else none
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine offsetMachine (move true)) scanMachine) (move false))
  eraseMachine

open CanonicalFourfoldRowProgram RepairRepresentation SupplierPipeline
open RepairSource.CloseoutFinal

end
end NearCubicWires.P1Closure.RawRelabelRun
