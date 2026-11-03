import Proof.Packets.AddressedAtomProgram
import Proof.Packets.PhysicalRepeatStep

/-! Every active iteration of the fixed dense-table loop executes the
checked indexed atom worker. Its count, keys, source cursors and all table
bytes are the exact states of AddressedAtomProgram. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomProgram
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair word cacheWord)
open PacketVector (Packet)

def H (coding : Nat→Nat) (cs : List Pair) (j : Nat) := NativeIndexedAtom.heads 0 (codePrefix coding cs j).length
def A (C R : Nat) (coding : Nat→Nat) (cs : List Pair) (initial : List Packet) (j : Nat) :=
  NativeIndexedAtom.data C R (cacheWord cs) (codes coding cs)
    (PacketVector.bank R (table C coding cs initial j)) (index cs j)

end PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomProgram
