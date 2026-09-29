import Proof.CaseAnalysis.WitnessTermRead

/-! The term reader's reusable bank is cleared in one paid sweep. Its
original coefficient width and the canonical stream cursor are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRead
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots (i : Fin 721) : Fin 725:=
  if i.val<149 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
noncomputable def eraser:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 719)

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRead
