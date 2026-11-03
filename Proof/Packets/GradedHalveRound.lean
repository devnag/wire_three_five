import Proof.PCP.PCPTraversalSplit
import Proof.PCP.PCPUnaryCopy
import Proof.Amplification.RecoveryScratchErase
import Proof.Packets.PhysicalRepeatStep

/-! An independently checked reusable physical ceiling-halving round. The
construction follows the original WindowHalveRoundK split/erase/copy/erase
sequence, using its authentic primitive workers without importing the unrelated
window-emitter application chain. No schedule or source is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.GradedHalveRound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open RecoveryExecution RecoveryRootRound NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section


/-! ## The reusable erase, in `ClockJoin` form with a round-tripping log -/

/-! ## The four docked stages -/

def splitSlots : Fin 4→Fin 6:=![0,1,2,3]
def clearSlots : Fin 3→Fin 6:=![0,5,4]
def copySlots : Fin 3→Fin 6:=![1,0,4]
def resetSlots : Fin 4→Fin 6:=![1,2,5,4]


noncomputable def splitStage:=RecoveryFocus.machine splitSlots PCPUnarySplit.machine
noncomputable def clearStage:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def copyStage:=RecoveryFocus.machine copySlots PCPUnaryCopy.machine
noncomputable def resetStage:=RecoveryFocus.machine resetSlots (RecoveryScratchErase.resetMachine 2)

/-! ## The round -/

noncomputable def round:=
  Composition.machine (Composition.machine (Composition.machine splitStage clearStage) copyStage)
    resetStage

end
end PCJ9eff70d512234a4c_Fixed.Materializer.GradedHalveRound
