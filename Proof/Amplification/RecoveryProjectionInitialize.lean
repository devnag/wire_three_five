import Proof.Amplification.RecoveryProjectionInitializeBank

/-! The whole actual row initializer allocates scratch, writes all R random
bits, and positions both finite repeat drivers. Its input contains only the
source and physically produced capacity and dimension words. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionInitialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readyHeads (i : Fin 36) := if i.val=34 ∨ i.val=35 then 1 else 0
def position : Machine 36 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,
    fun i=>if i.val=34 ∨ i.val=35 then .right else .stay⟩ else none

theorem position_step (data : Fin 36→List Bool) :
    step position (initialConfiguration position data)=some ⟨1,readyHeads,data⟩ := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val=34 ∨ i.val=35 <;> simp [applyAction,readyHeads,hi,HeadMove.apply,initialConfiguration]
  · rfl


end NearCubicWires.RepairSource.RecoveryProjectionInitialize
