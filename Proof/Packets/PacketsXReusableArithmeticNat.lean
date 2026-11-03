import Proof.Packets.NormalizedAdditionData
import Proof.Packets.NormalizedMultiplyData
import Proof.Packets.NormalizerCold
import Proof.Packets.PacketsXNormalizerOperations
import Proof.Packets.ReusableArithmeticLeft
import Proof.Packets.ReusableNormalizedArithmetic
import Proof.Packets.PacketsXNormalizedFiniteTransport

/-! Reusable arithmetic on the unchanged natural literal codes. The physical
finite alphabet is only a checked bound; no renumbering is performed. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NormalizedFiniteTransport

def natState (C R : Nat) (P Q : Ring.Poly Nat) := state C R (P.map (maskNat C)) (Q.map (maskNat C))


end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
