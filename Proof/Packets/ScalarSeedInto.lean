import Proof.Packets.ScalarCounterSeed
import Proof.Packets.PhysicalIndexReload

/-! Place the physically initialized binary-zero scalar in any ambient bank.
The all-zero-head variant pays both width-driver head moves. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ScalarSeedInto
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slots {t : Nat} (scalar log width : Fin t) : Fin 3→Fin t := ![width,scalar,log]
def machine {t : Nat} (scalar log width : Fin t) := RecoveryFocus.machine (slots scalar log width) ScalarCounterSeed.machine
def zeroMachine {t : Nat} (scalar log width : Fin t) :=
  Composition.machine (PhysicalIndexReload.move width .right)
    (Composition.machine (machine scalar log width) (PhysicalIndexReload.move width .left))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ScalarSeedInto
