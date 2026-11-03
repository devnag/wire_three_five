import Proof.Packets.ScalarTwice
import Proof.Packets.PhysicalIndexReload

/-! Canonical ambient-bank adapters for actual scalar production. Only the
selected scalar word changes; the count source and rewind allocation survive. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ScalarTwiceInto
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slots {t : Nat} (scalar log counter : Fin t) : Fin 3→Fin t := ![scalar,log,counter]
def machine {t : Nat} (scalar log counter : Fin t) := RecoveryFocus.machine (slots scalar log counter) ScalarTwice.machine
def zeroMachine {t : Nat} (scalar log counter : Fin t) :=
  Composition.machine (PhysicalIndexReload.move counter .right)
    (Composition.machine (machine scalar log counter) (PhysicalIndexReload.move counter .left))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ScalarTwiceInto
