import Proof.CaseAnalysis.RowsModeHashPosition

/-! The next Toeplitz row derives its cursor positions from its own
incremented unary template, retaining the same original seed tapes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashPrepare
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch CloseoutRowsModeHashReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowSlot : Fin 1→Fin 8:=fun _=>4
def positionSlots : Fin 3→Fin 8:=![4,2,5]
noncomputable def advance:=RecoveryFocus.machine rowSlot CloseoutRowsDegreeAdvance.templateMachine
noncomputable def position:=RecoveryFocus.machine positionSlots CloseoutRowsModeHashPosition.machine
noncomputable def machine:=Composition.machine advance position

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashPrepare
