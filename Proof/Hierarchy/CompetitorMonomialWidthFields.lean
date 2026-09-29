import Proof.Hierarchy.CompetitorMonomialClear

/-! The three runtime scalar widths are copied from retained physical unary
words into the cleared multiplication/normalization workspace. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def widthSource : Fin 3 → Fin 88 := ![81,82,83]
def widthTarget : Fin 3 → Fin 88 := ![6,67,75]
def widthSlots (j : Fin 3) : Fin 4 → Fin 88 := ![widthSource j,86,widthTarget j,87]
noncomputable def widthProgram (j : Fin 3) := RecoveryFocus.machine (widthSlots j) ClockUnarySum.machine

def widthStates : List (Fin 3) → ℕ
  | [] => 1
  | _::js => 5+widthStates js
noncomputable def widthsProgram : (js : List (Fin 3)) → Machine 88 (widthStates js)
  | [] => fieldHalt
  | j::js => Composition.machine (widthProgram j) (widthsProgram js)

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
