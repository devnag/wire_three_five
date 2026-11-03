import Proof.CaseAnalysis.RowsModeParity
import Proof.MachineModel.OrdinaryRewindWorkspace
import Proof.Amplification.RecoveryFocusDock

/-! The actual binomial parity scan pays its recorded return, retaining
both scalar frames and the accumulated guard for the next coefficient. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeParityReusable
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Rewind.machine CloseoutRowsModeParity.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsModeParityReusable
