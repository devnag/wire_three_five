import Proof.Packets.IdentityAtomMaterialize
import Proof.Packets.IdentityCodeCache
import Proof.Packets.AddressedAtomMaterialize
import Proof.Packets.PacketsXCycleDenseAtomCost
import Proof.Packets.PacketsXDenseAtomBoundary

/-! All individual parser, normalization, output-cache and indexed-write
capacity guards of the identity materializer follow from the actual atom
shape and common reserve. Paid outer counter moves restore the provider's
uniform head boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomBounded
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair)
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost
attribute [local irreducible] IdentityAtomMaterialize.machine

noncomputable def machine := Composition.machine (DenseAtomBoundary.move .right)
  (Composition.machine IdentityAtomMaterialize.machine (DenseAtomBoundary.move .left))
attribute [local irreducible] machine

end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomBounded
