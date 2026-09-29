import Proof.Hierarchy.CompetitorSumConstants

/-! The initial scalar workspace is physically zeroed from blank tapes.
Its reset counter also starts blank; no initial capacity padding is assumed. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coldSlot (j : Fin 89) : Fin 94 :=
  if j.val<6 then ⟨j.val,by omega⟩
  else if j.val<83 then ⟨j.val+1,by omega⟩
  else if j.val<86 then ⟨j.val+2,by omega⟩
  else if j.val=86 then 89 else if j.val=87 then 92 else 93
def coldInput (b : ℕ) (source : List Bool) : Fin 94 → List Bool := fun i =>
  if i.val=6 then List.replicate (width b) true
  else if i.val=84 then List.replicate b true else if i.val=88 then source
  else if i.val=90 then List.replicate (capacity b) true else []
noncomputable def coldClearProgram := clearProgram coldSlot


end NearCubicWires.RepairOrdinary.CompetitorSumFold
