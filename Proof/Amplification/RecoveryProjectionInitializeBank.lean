import Proof.Amplification.RecoveryProjectionNormalizedRows

/-! One actual unary sweep allocates all 28 evaluator tapes and the shared
copy log. Source fields and the already produced R/Q drivers are retained. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionInitialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots (i : Fin 31) : Fin 36 :=
  ⟨if i.val<28 then i.val else if i.val=28 then 30 else if i.val=29 then 32 else 33,
    by split_ifs <;> omega⟩
theorem erase_injective : Function.Injective eraseSlots := by
  intro a b h; apply Fin.ext
  have hv:=congrArg (fun i : Fin 36=>i.val) h
  dsimp only [eraseSlots] at hv
  split_ifs at hv <;> have ha:=a.isLt <;> have hb:=b.isLt <;> omega


end NearCubicWires.RepairSource.RecoveryProjectionInitialize
