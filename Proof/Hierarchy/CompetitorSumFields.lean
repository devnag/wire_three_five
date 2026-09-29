import Proof.Hierarchy.CompetitorSumErase

/-! Actual field loading on the scalar-fold register layout. The global term
stream advances; all local heads return, and every field call is paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def target (j : Fin 6) : Fin 94 := j.castAdd 88
def loadSlots (j : Fin 6) : Fin 3 → Fin 94 := ![88,target j,89]
noncomputable def fieldProgram (j : Fin 6) := RecoveryFocus.machine (loadSlots j) FrameLoad.machine

def fieldStates : List (Fin 6) → ℕ
  | [] => 1
  | _::js => 4+fieldStates js
def fieldHalt : Machine 94 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
noncomputable def fieldsProgram : (js : List (Fin 6)) → Machine 94 (fieldStates js)
  | [] => fieldHalt
  | j::js => Composition.machine (fieldProgram j) (fieldsProgram js)
def fieldStream (fields : Fin 6 → List Bool) (js : List (Fin 6)) := js.flatMap (fun j => frame (fields j))


end NearCubicWires.RepairOrdinary.CompetitorSumFold
