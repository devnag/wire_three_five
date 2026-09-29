import Proof.Supplier.RowMaskBody

/-! A selected incidence mask is consumed once. Its selected positions are
appended in order and its population is added to the physical count tape. -/
namespace NearCubicWires.RepairOrdinary.RowMaskLoop
open LocalBitMultitape RecoveryExecution RowMaskBodyParts Streaming RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine RowMaskBody.machine (fun _ _=>true)

end NearCubicWires.RepairOrdinary.RowMaskLoop
