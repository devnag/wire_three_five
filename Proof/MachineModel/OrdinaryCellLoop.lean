import Proof.MachineModel.OrdinaryStreamController

/-! A whole bucket's cell scan over a framed rank stream. The fixed program
loads each rank, computes and appends its bit, and retains bounded workspace
for the next record. Production of this rank stream is a separate caller. -/
namespace NearCubicWires.RepairOrdinary.CellLoop
open LocalBitMultitape SignedSortKey
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CellLoop
