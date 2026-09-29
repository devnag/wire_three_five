import Proof.Hierarchy.CompetitorRawFieldEmit

/-! A fixed sequence of physical scalar-field appends. The source wiring
may reuse a field; its head is restored before each subsequent call. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def states {t : ℕ} : List (Fin t) → ℕ
  | [] => 1
  | _::js => 4+states js
def halt (t : ℕ) : Machine t 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
noncomputable def listProgram {t : ℕ} (target counter : Fin t) : (js : List (Fin t)) → Machine t (states js)
  | [] => halt t
  | j::js => Composition.machine (program j target counter) (listProgram target counter js)
def listCost {t : ℕ} (fields : Fin t → List Bool) : List (Fin t) → ℕ
  | [] => 0
  | j::js => 4*(fields j).length+4+listCost fields js


end NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit
