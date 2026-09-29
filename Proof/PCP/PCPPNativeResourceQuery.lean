import Proof.PCP.PCPPNativeResourceQueryLayout

/-! The cold native query executor derives its shared C/F/G and exact
counts physically from the SAME source counts and measured stream masses.
It retains the metadata used by the ensuing clause/header/tail caller. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeResourceQuery
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def output (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width ≤ R) (hQ : p.queries ≤ Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) (suffix : List Bool) (W : ℕ) :=
  PCPPNativeQueryLoop.templateConfiguration 3 (PCPPNative.descriptor oracle)
    (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix)
    (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length (Q*(2*oracle.size+1))
    (PCPPNativeCapacityReady.C W) (PCPPNativeCapacityReady.F W) (PCPPNativeCapacityReady.G W)
    ((PCPPNative.queryNodesPrefix 0 oracle ((p.normalized R Q hR hQ).queryAddressBits x) Q).flatMap
      PCPPRequestNodeSchema.native) R Q 1

end NearCubicWires.RepairOrdinary.PCPPNativeResourceQuery
