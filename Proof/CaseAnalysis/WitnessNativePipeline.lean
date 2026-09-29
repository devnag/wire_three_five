import Proof.CaseAnalysis.WitnessNativePolicyDock

/-! One original stream traversal reaches the exact size test. The native
node/source/cache/policy continuation runs only on its successful branch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev base (G : ℕ):=125+OracleCap.Call.extra G
def counter (G : ℕ):=NativeScreen.slots G
def localSlots (a : PointwisePCPPAlgorithm) (D G : ℕ):=NativePolicy.Call.slots a D (counter G)
def cacheSlots (a : PointwisePCPPAlgorithm) (D G : ℕ) (j : Fin (PCPPSourceCache.tapes a)):=
  localSlots a D G (NativePolicy.cacheSlots a D j)
def flagSlot (a : PointwisePCPPAlgorithm) (D G : ℕ):=NativePolicy.Call.old a D (NativeScreen.flagSlot G)
def first (a : PointwisePCPPAlgorithm) (D G : ℕ):=
  TapeEmbedding.machine (NativePolicy.Call.extra a D) (NativeScreen.machine G)
def second (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ):=
  NativePolicy.Call.machine a D copies delta (counter G)
def test (a : PointwisePCPPAlgorithm) (D G : ℕ) (scan : Fin (base G+NativePolicy.Call.extra a D)→Bool):=
  scan (flagSlot a D G)
def machine (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ):=
  CloseoutRowsGateColdPair.machine (first a D G) (second a D G copies delta) (test a D G)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline
