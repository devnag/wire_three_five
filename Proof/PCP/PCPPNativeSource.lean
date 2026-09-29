import Proof.PCP.PCPPNativeSourceLayout

/-! A checked cold native emitter is followed by paid framing, the exact
one PCPP source call, and physical shared-cache setup. Domain and size come
from that emitter's actual retained tapes; no prepared source input is added. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeSource
open LocalBitMultitape RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) (nativeFuel : ℕ) :=
  6*nativeFuel+8+PCPPSourceCache.totalBudget a request

end NearCubicWires.RepairOrdinary.PCPPNativeSource
