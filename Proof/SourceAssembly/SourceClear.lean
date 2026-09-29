import Proof.SourceAssembly.SourceBundle

/- A paid parallel saturating rewind and erase of the disposable source bank.
The true driver and false log are retained exactly for the next request. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ6e421fabe2aa4155_SourceClear
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound
noncomputable section

def join {t : Nat} {α : Type} (a : Fin t → α) (b c : α) : Fin (t+1+1) → α :=
  Fin.addCases (Fin.addCases a (fun _ : Fin 1 => b)) (fun _ : Fin 1 => c)

def driver (t : Nat) : Fin (t+1+1) := ((0 : Fin 1).natAdd t).castAdd 1
def logPort (t : Nat) : Fin (t+1+1) := (0 : Fin 1).natAdd (t+1)

def rewind (t : Nat) : Machine (t+1+1) 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q scan => if q.val=0 then
    some (if scan (driver t) then
      ⟨0,join (fun _ => none) none (some true),join (fun _ => .left) .right .right⟩
    else ⟨1,fun _ => none,join (fun _ => .stay) .stay .left⟩)
    else if q.val=1 then some (if scan (logPort t) then
      ⟨1,join (fun _ => none) none (some false),join (fun _ => .stay) .left .left⟩
    else ⟨2,fun _ => none,fun _ => .stay⟩) else none

end
end PCJ6e421fabe2aa4155_SourceClear
