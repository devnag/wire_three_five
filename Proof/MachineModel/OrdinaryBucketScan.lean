import Proof.MachineModel.OrdinaryCellLoop

/-! A whole signed B.3 bucket-column scan at the unchanged capacity bucket.
The actual loop consumes framed canonical ranks in the supplied row order;
producing that rank stream and final coordinate ordering remain caller work. -/
namespace NearCubicWires.RepairOrdinary.CellLoop
open LocalBitMultitape SupplierPrinter SignedSortKey LeftPlaneCell
open RecordController (test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CellLoop
