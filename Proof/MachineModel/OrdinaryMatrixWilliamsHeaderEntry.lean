import Proof.MachineModel.OrdinaryMatrixPowerHeader

/-! The paid canonical Williams header on the same original-request run
that produced both matrices and the first signed coefficient plane. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsHeaderEntry
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def budget (r : Request) := MatrixFirstSignedPlane.budget r+1+(6*r.d+14)


end NearCubicWires.RepairOrdinary.MatrixWilliamsHeaderEntry
