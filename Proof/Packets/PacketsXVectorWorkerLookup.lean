import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.VectorControllerLayout
import Proof.Rows.PhysicalFocusBoundary
import Proof.Packets.VectorChildLookup
import Proof.Packets.PacketVector

/-! Actual final-coordinate lookup into the right arithmetic operand, retaining
the full provider state, both vector banks, and all live counters. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def lookupSlots (j : Fin 37) : Fin 296:=childSlots (j.castAdd 2)
def lookupRight:=RecoveryFocus.machine lookupSlots VectorChildLookup.machine

attribute [local irreducible] VectorChildLookup.machine lookupRight

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
