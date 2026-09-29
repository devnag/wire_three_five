import Proof.Hierarchy.CompetitorRationalSum

/-! Two physical clears used by the scalar fold: the non-accumulator
workspace before each term, and the three old accumulator cells before
copyback. Both use the same retained unary driver and reset word. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend {k : ℕ} (slot : Fin k → Fin 94) : Fin (k+2) → Fin 94 :=
  Fin.addCases (m := k+1) (n := 1) (motive := fun _ => Fin 94)
    (Fin.addCases (m := k) (n := 1) (motive := fun _ => Fin 94) slot (fun _ => 90)) (fun _ => 91)
noncomputable def clearProgram {k : ℕ} (slot : Fin k → Fin 94) :=
  RecoveryFocus.machine (extend slot) (RecoveryScratchErase.resetMachine k)

def workSlot (j : Fin 83) : Fin 94 :=
  if j.val<2 then ⟨j.val+2,by omega⟩ else if j.val=2 then 5
  else if j.val<80 then ⟨j.val+4,by omega⟩ else ⟨j.val+5,by omega⟩
def accumulatorSlot : Fin 3 → Fin 94 := ![0,1,4]

end NearCubicWires.RepairOrdinary.CompetitorSumFold
