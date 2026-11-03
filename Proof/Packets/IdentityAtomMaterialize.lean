import Proof.Packets.IdentityAtomPrepare

/-! Actual identity-code generation followed by the normalized occurrence
atom materializer. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomMaterialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open PacketVector (Packet)
open AddressedAtomMaterialize (H paddedA)
attribute [local irreducible] AddressedAtomMaterialize.machine IdentityCodeCache.machine prepare

noncomputable def machine := Composition.machine prepare AddressedAtomMaterialize.machine
attribute [local irreducible] machine

end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomMaterialize
