import Proof.CaseAnalysis.WitnessNativeScreen

/-! The guarded measured fields feed the original node emitter, its exact
typed descriptor, and one faithful PCPP call with the reusable cache. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeCache
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def nativeMachine:=TapeEmbedding.machine 1 PCPPNativeClauseOracle.machine
def machine (a : PointwisePCPPAlgorithm):=
  PCPPNativeClauseDescriptorConsumer.sourceMachine a nativeMachine 102 363 16 14
def cacheSlots (a : PointwisePCPPAlgorithm) (j : Fin (PCPPSourceCache.tapes a)):=
  PCPPNativeClauseDescriptorConsumer.cacheSlots a (363 : Fin 364) 16 14 j
def request (a : PointwisePCPPAlgorithm) (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width≤R) (hQ : p.queries≤Q) {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R):=
  PCPPRequestBoundary.request a (PCPPNativeCompactNodes.circuit p R Q hR hQ x oracle)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeCache
