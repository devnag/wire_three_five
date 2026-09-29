import Proof.CaseAnalysis.WitnessNativeCache
import Proof.CaseAnalysis.WitnessSourcePolicyCall

/-! The original guarded native continuation produces the cache and its
one-time actual V, clause count, q0 and coefficient-width policy together. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev base (a : PointwisePCPPAlgorithm):=
  PCPPNativeSource.tapes a (PCPPNativeClauseDescriptorConsumer.tapes 364)
def fields (a : PointwisePCPPAlgorithm) : Fin 2→Fin (base a):=
  ![NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a 0),
    NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a 13)]
def cacheSlots (a : PointwisePCPPAlgorithm) (D : ℕ) (j : Fin (PCPPSourceCache.tapes a)):=
  SourcePolicy.Call.old D (NativeCache.cacheSlots a j)
def policySlots (a : PointwisePCPPAlgorithm) (D : ℕ):=SourcePolicy.Call.slots D (fields a)
def first (a : PointwisePCPPAlgorithm) (D : ℕ):=
  TapeEmbedding.machine (SourcePolicy.Call.extra D) (NativeCache.machine a)
def second (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ):=
  SourcePolicy.Call.machine D copies delta (fields a)
def machine (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ):=
  Composition.machine (first a D) (second a D copies delta)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy
