import Proof.MachineModel.OrdinaryRecordLoop

/-! The annotated-record loop consumes the exact existing rank-annotator
output word. This closes the encoding boundary, without assuming that its
production or the scalar bucket/mask inputs are free. -/
namespace NearCubicWires.RepairOrdinary.LabelledScan
open LocalBitMultitape
open RecordCell (config)
open RecordController (test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.LabelledScan
