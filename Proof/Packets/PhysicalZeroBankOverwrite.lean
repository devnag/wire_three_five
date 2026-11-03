import Proof.Packets.PhysicalZeroBank
import Proof.Packets.MaskConstant
import Proof.Packets.PhysicalBankCopy

/-! The same fixed zero-bank machine resets an existing dense table. Every
old bit is overwritten and the cursor is physically returned. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch

attribute [local irreducible] chunk packet loop machine

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroBank
