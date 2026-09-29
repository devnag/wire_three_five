import Proof.Hierarchy.CompetitorUnaryWidthCopy

/-! Actual coefficient/count loading for the monomial stream loop. The
coefficient cursor advances while the scalar-output cursor is preserved;
every local field call and handoff is paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (outPos pos : ℕ) : Fin 88 → ℕ := fun i => if i.val=79 then pos else if i.val=74 then outPos else 0
def cfg {s : ℕ} (outPos : ℕ) (q : Fin s) (pos : ℕ) (ambient : Fin 88 → List Bool) : Configuration 88 s :=
  ⟨q,heads outPos pos,ambient⟩

def target (j : Fin 6) : Fin 88 := j.castAdd 82
def loadSlots (j : Fin 6) : Fin 3 → Fin 88 := ![79,target j,80]
noncomputable def fieldProgram (j : Fin 6) := RecoveryFocus.machine (loadSlots j) FrameLoad.machine

def fieldStates : List (Fin 6) → ℕ
  | [] => 1
  | _::js => 4+fieldStates js
def fieldHalt : Machine 88 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
noncomputable def fieldsProgram : (js : List (Fin 6)) → Machine 88 (fieldStates js)
  | [] => fieldHalt
  | j::js => Composition.machine (fieldProgram j) (fieldsProgram js)
def fieldStream (fields : Fin 6 → List Bool) (js : List (Fin 6)) := js.flatMap (fun j => frame (fields j))


end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
