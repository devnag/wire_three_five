import Proof.Hierarchy.CompetitorSameBucketNativeFields

/-! The complete cold Request/W through all actual same-bucket gate
candidate emissions. Internal rank/coefficient cursors are left consumed;
the retained original input and growing output have the advertised ABI. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdGate
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open CompetitorSameBucketColdNativeLayout (slots entry ambient)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def gate:=RecoveryFocus.machine slots CompetitorSameBucketGateLoop.machine
noncomputable def tail:=Composition.machine CompetitorSameBucketColdNativeLayout.advance gate
noncomputable def machine:=Composition.machine CompetitorSameBucketColdInitialized.machine tail
def input:=CompetitorSameBucketColdInitialized.input
noncomputable def budget (r : Request):=CompetitorSameBucketColdInitialized.budget r+1+
  (1+1+CompetitorSameBucketGateLoop.budget r (CompetitorSameBucketBucketBody.scalarCapacity r) r.Gates)

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdGate
