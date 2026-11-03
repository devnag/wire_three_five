import Proof.Rows.MaskProductBody

/-! Constant polynomial banks are physically generated from the runtime
width template. No all-false mask or result-count word is supplied as input. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskConstant
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def maskMachine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q scan=>if q.val=0 then
    some (if scan 0 then ⟨0,![none,some false],![.right,.right]⟩
      else ⟨1,fun _=>none,![.left,.stay]⟩)
    else if q.val=1 then
      some (if scan 0 then ⟨1,fun _=>none,![.left,.left]⟩
        else ⟨2,fun _=>none,![.right,.stay]⟩)
    else none

def countMachine (one : Bool) : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q _=>if q.val=0 then
    some ⟨if one then 1 else 2,fun _=>some false,fun _=>.right⟩
    else if q.val=1 then some ⟨2,fun _=>some true,fun _=>.stay⟩
    else none

noncomputable def countSlots : Fin 1→Fin 3 := ![2]
noncomputable def oneMachine := Composition.machine (TapeEmbedding.machine 1 maskMachine)
  (RecoveryFocus.machine countSlots (countMachine true))

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskConstant
