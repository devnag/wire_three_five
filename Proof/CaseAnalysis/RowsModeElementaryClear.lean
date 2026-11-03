import Proof.CaseAnalysis.RowsModeElementaryReset
import Proof.Amplification.RecoveryScratchErase
import Proof.Hierarchy.HierarchyAllocation

/-! The original C driver clears the elementary work bank and its recording
log. The output, four numeric masters and all unrelated heads are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryClear
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def saved (i : Fin 45) : Fin 52:=if h:i.val<44 then ⟨i.val,by omega⟩ else 45
def slots : Fin 47→Fin 52:=Fin.addCases (m:=45) (n:=2) (motive:=fun _=>Fin 52) saved ![50,51]
noncomputable def machine:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 45)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryClear
