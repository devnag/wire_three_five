import Proof.Packets.ReusableNormalizedArithmetic
import Proof.Packets.PacketBankZeroHeads
import Proof.Packets.ArithmeticPacketLookup

/-! Actual indexed child lookup into the reusable right operand. The bank,
physical index, current left operand, and reserve resources are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildLookup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slots : Fin 6→Fin 37 := ![31,34,26,27,35,36]
def machine := RecoveryFocus.machine slots PacketBank.lookupZero

attribute [local irreducible] PacketBank.lookupZero PacketBank.lookup

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildLookup
