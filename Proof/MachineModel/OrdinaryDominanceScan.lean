import Proof.MachineModel.OrdinaryLabelledScan

/-! The actual annotated-record cell scan at the paper's sorted dominance
occurrences. Bits at A-occurrence positions are exactly the signed left
matrix entries; retaining/selecting their row identifiers is subsequent work. -/
namespace NearCubicWires.RepairOrdinary.LabelledScan
open LocalBitMultitape SupplierPrinter SignedSortKey LeftPlaneCell
open RecordCell (config)
open RecordController (test)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.LabelledScan
