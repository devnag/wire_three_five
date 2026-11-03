import Proof.Packets.AddressedAtomPadded
import Proof.Packets.IdentityCodeCache

/-! The final occurrence-address atom bank is produced from its actual
native source cache and count. Identity code bytes are physically generated,
then consumed by the same checked normalized dense-table materializer. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomMaterialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open PacketVector (Packet)
open AddressedAtomMaterialize (H paddedA)
attribute [local irreducible] IdentityCodeCache.machine

def slots : Fin 6→Fin 46 := ![44,40,45,33,34,35]
noncomputable def lower := PhysicalIndexReload.move (44 : Fin 46) .left
noncomputable def raise := PhysicalIndexReload.move (44 : Fin 46) .right
noncomputable def cache := RecoveryFocus.machine slots IdentityCodeCache.machine
noncomputable def prepare := Composition.machine lower (Composition.machine cache raise)
attribute [local irreducible] prepare


end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomMaterialize
