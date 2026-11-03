import Mathlib.Data.Nat.Choose.Lucas
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.Amplification.RecoveryReadyCalls
import Proof.MachineModel.Runs

/-! A physical simultaneous scan of two equal-width binary fields computes
the Lucas guard. No numerical binomial value or Pascal table is allocated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeParity
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then
      some ⟨if bits 0 then 1 else 2,fun _=>none,![.right,.right,.stay]⟩
    else if q=1 then
      some ⟨0,![none,none,some (bits 2&&(!bits 1||bits 0))],![.right,.right,.stay]⟩
    else none

end NearCubicWires.RepairOrdinary.CloseoutRowsModeParity
