import Proof.MachineModel.OrdinaryMatrixSignedMaskBounds

/-! A whole original-request execution produces its first exact signed
Williams left plane. The positive p guard is explicit; the all-plane
scheduler owns the zero-p branch and subsequent signed/bit iterations. -/
namespace NearCubicWires.RepairOrdinary.MatrixFirstSignedPlane
open LocalBitMultitape MatrixScoreBatch MatrixSignedEntry
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def budget (r : Request) := MatrixSignedEntry.budget r+1+MatrixSignedMaskPass.budget r

end NearCubicWires.RepairOrdinary.MatrixFirstSignedPlane
