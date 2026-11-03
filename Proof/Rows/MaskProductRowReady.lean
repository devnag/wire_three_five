import Proof.Rows.MaskProductRow

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

abbrev last := TapeEmbedding.machine 1 PhysicalSupportReturn.machine
abbrev machine := Composition.machine raw last

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
