import Proof.PCP.PCPPNativeClauseDescriptorConsumer

/-! The actual original node emitter feeds the typed descriptor and the
single faithful PCPP source call, ending in its physically prepared cache. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptorConsumer
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def sourceMachine (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s)
    (target width size index : Fin t) :=
  PCPPNativeSource.machine a (machine a p target width size index)
    (slots width size index 26) (slots width size index 27) (slots width size index 10)
def sourceBudget (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) (fuel : ℕ) :=
  PCPPNativeSource.budget a (PCPPRequestBoundary.request a c) (budget a c fuel)
def cacheSlots (a : PointwisePCPPAlgorithm) {t : ℕ} (width size index : Fin t)
    (j : Fin (PCPPSourceCache.tapes a)) :=
  PCPPNativeSource.sourceSlots a (slots width size index 27) (slots width size index 10) j

end NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptorConsumer
