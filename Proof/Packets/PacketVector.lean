import Proof.Packets.PacketBankLookup
import Proof.Packets.PacketBankPrimitives

/-! Actual indexed access and append for materialized polynomial vectors.
Each resident entry stores the mask bank followed by its physical unary count,
with the same paid R-bit reserve used by the reusable arithmetic workers. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketVector
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

abbrev Packet := List (List Bool)
def payload (R : Nat) (P : Packet) : List Bool := ZeroPadding.pad R P.flatten
def count (R : Nat) (P : Packet) : List Bool := ZeroPadding.pad R (CompareMachine.word P.length)
def entry (R : Nat) (P : Packet) : List Bool := payload R P++count R P
def bank (R : Nat) (ps : List Packet) : List Bool := ps.flatMap (entry R)


end PCJ9eff70d512234a4c_Fixed.Materializer.PacketVector
