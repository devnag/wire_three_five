import Proof.Packets.PacketsXIdentityAtomBounded

/-! The final occurrence-to-pool table uses arbitrary raw source atom pairs.
All copy, native parsing, normalization and whole-cache space guards follow
from the actual raw count, degree and index bounds. No singleton restriction
is imposed on these atoms. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomGeneralBounded
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair word cacheWord)
open Theorem25Completion.CycleBounds
attribute [local irreducible] IdentityAtomMaterialize.machine IdentityAtomBounded.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomGeneralBounded
