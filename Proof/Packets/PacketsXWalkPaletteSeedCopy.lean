import Proof.Packets.PhysicalTripleCopy
import Proof.Packets.PacketsXWalkSeedResident

/-! Route the resident walk decoder's three actual words into the literal
palette. The fifteen-tape walk bank precedes the 316-tape palette arena. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 15000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkPaletteSeedCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

def slots : Fin 7 → Fin 331 := ![17,11,12,13,21,22,23]
def machine := RecoveryFocus.machine slots PhysicalTripleCopy.machine

end
end Theorem25Completion.WalkPaletteSeedCopy
