import Proof.Hierarchy.CompetitorThresholdAmbient

/-! The computed accumulator and the physically printed fixed constants
are wired into the literal rational comparison after the paid native clear.
The retained zero padding differs between accumulated and fresh fields. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def decisionSlots (lower : Bool) (i : Fin 67) : Fin 110 :=
  if h : i.val<7 then
    (if lower then ![0,1,96,101,4,106,6] else ![96,101,0,1,106,4,6]) ⟨i.val,h⟩
  else ⟨i.val,by omega⟩
noncomputable def decisionProgram (lower : Bool) :=
  RecoveryFocus.machine (decisionSlots lower) CompetitorRationalDecision.machine

end NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
