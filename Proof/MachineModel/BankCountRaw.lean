import Proof.MachineModel.BankCountConsumer
import Proof.MachineModel.Layout

/-! The original incidence printer runs in the count-metadata bank. Its
actual count and table are retained; the twelve new private tapes are idle. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawOld (i : Fin 116) : Fin 128:=i.castAdd 12
noncomputable def raw:=RecoveryFocus.machine rawOld BankExecution.machine


end NearCubicWires.ExtIncidence.BankCount
