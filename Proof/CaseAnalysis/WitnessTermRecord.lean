import Proof.CaseAnalysis.WitnessCoefficientRecord

/-! The retained coefficient stream shares the term loader's restored
scratch tape. Its only new tape is the output, at its logical cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRecord
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5→Fin 827:=![316,690,693,826,723]
noncomputable def machine:=RecoveryFocus.machine slots CoefficientRecord.machine

def word (b : ℕ) (q : ℚ):=frame [decide (q.num<0)]++
  frame (SignedSortKey.binary b q.num.natAbs)++frame (SignedSortKey.binary b q.den)

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRecord
