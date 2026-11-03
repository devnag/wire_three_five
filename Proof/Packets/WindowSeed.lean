import Proof.Packets.WindowSeedClear
import Proof.Packets.WindowSeedBody

/-! Complete physical cold/reentry initialization of the fixed window
bank from actual resident numeric metadata and the common reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def driverSlot : Fin 1→Fin 69 := ![61]
def lower := RecoveryFocus.machine driverSlot (Completion.PhysicalDriverMoves.machine 1 .left)
def raise := RecoveryFocus.machine driverSlot (Completion.PhysicalDriverMoves.machine 1 .right)
def machine := Composition.machine lower (Composition.machine clear (Composition.machine body raise))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
