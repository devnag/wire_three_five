import Proof.CaseAnalysis.RowsModeWindowEmit
import Proof.MachineModel.Layout

/-! Both scalar coefficient scans execute in the retained numeric bank,
leaving the live polynomial cursor and elementary masters unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowScalar
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsModeWindowLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RecoveryFocus.machine guardSlots CloseoutRowsModeWindowGuard.machine

noncomputable def summand:=Composition.machine machine CloseoutRowsModeWindowEmit.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowScalar
