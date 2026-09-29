import Proof.PCP.PCPPSourceCacheLayout

/-! One original native descriptor, one source call, then the physically
allocated shared query bank. No source work tape is rewound or assumed blank. -/
namespace NearCubicWires.RepairOrdinary.PCPPSourceCache
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def setupBudget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :=
  PCPPQueryCold.coefficient (degree a) (PCPPQueryCachedBounds.coefficient a)*
    (r.circuit.size+r.arity+1)^(degree a+1)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :=
  PCPPRequestSource.budget a r+1+setupBudget a r
def cacheSlots (a : PointwisePCPPAlgorithm) (j : Fin 19) :=
  coldSlots a (PCPPQueryCold.cacheSlots (degree a) j)

end NearCubicWires.RepairOrdinary.PCPPSourceCache
