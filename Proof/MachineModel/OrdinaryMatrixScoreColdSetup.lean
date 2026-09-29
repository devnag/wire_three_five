import Proof.MachineModel.OrdinaryMatrixScoreFields

/-! The original raw headers now physically produce every native initial
field and counter needed by the all-2U score traversal. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreColdSetup
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (d p : ℕ) (suffix : List Bool) := MatrixScoreSetup.budget d p suffix+1+
  MatrixScoreColdFields.budget d (d+3) (MatrixScoreSetup.capacity d p)

end NearCubicWires.RepairOrdinary.MatrixScoreColdSetup
