import Proof.PCP.PCPPQueryColdBounds
import Proof.PCP.PCPPRequestSourceRuntime

/-! The one faithful source call is routed directly into the shared query
bank. The native emitter's actual arity and size counters stay outside it. -/
namespace NearCubicWires.RepairOrdinary.PCPPSourceCache
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def degree (a : PointwisePCPPAlgorithm) := PCPPQueryCachedBounds.degree a
def coldTapes (a : PointwisePCPPAlgorithm) := PCPPQueryCold.tapes (degree a)
def tapes (a : PointwisePCPPAlgorithm) := coldTapes a+PCPPRequestSource.tapes a
def coldSlots (a : PointwisePCPPAlgorithm) (j : Fin (coldTapes a)) : Fin (tapes a) := j.castAdd (PCPPRequestSource.tapes a)

theorem cold_lower (a : PointwisePCPPAlgorithm) : 38≤coldTapes a := by
  simp [coldTapes,PCPPQueryCold.tapes,PCPPQueryCapacity.tapes,RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]
  omega

def sourceSlots (a : PointwisePCPPAlgorithm) (j : Fin (PCPPRequestSource.tapes a)) : Fin (tapes a) :=
  if j.val=(PCPPRequestSource.outputSlot a).val then ⟨0,by have h:=cold_lower a; dsimp [tapes]; omega⟩
  else j.natAdd (coldTapes a)

noncomputable def sourceMachine (a : PointwisePCPPAlgorithm) := RecoveryFocus.machine (sourceSlots a) (PCPPRequestSource.machine a)
noncomputable def setupMachine (a : PointwisePCPPAlgorithm) := RecoveryFocus.machine (coldSlots a)
  (PCPPQueryCold.machine (degree a) (PCPPQueryCachedBounds.coefficient a))
noncomputable def machine (a : PointwisePCPPAlgorithm) := Composition.machine (sourceMachine a) (setupMachine a)

end NearCubicWires.RepairOrdinary.PCPPSourceCache
