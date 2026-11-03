import Proof.Packets.AddressedAtomIteration

/-! The physically counted complete dense-table pass; no per-iteration
execution premise appears in the final run theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomProgram
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open PacketVector (Packet)

noncomputable def machine := RepeatMachine.machine NativeIndexedAtom.machine (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomProgram
