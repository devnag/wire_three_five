import Proof.CaseAnalysis.WitnessNativeFields
import Proof.CaseAnalysis.RowsGateSourceCalls

/-! The original cold input/oracle prefix enters the guarded native
pipeline only after cutoff, actual-width and canonical-decoder success. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev tapes (a : PointwisePCPPAlgorithm) (k D G : ℕ):=base source k+NativePipeline.Dock.extra a D G
def old (a : PointwisePCPPAlgorithm) (k D G : ℕ) (i : Fin (base source k)):=NativePipeline.Dock.old a D G i
def slots (a : PointwisePCPPAlgorithm) (k D G : ℕ):=NativePipeline.Dock.slots a D G (fields source k)
def cacheSlots (a : PointwisePCPPAlgorithm) (k D G : ℕ) (j : Fin (PCPPSourceCache.tapes a)):=
  slots source a k D G (NativePipeline.cacheSlots a D G j)
def lengthSlot (a : PointwisePCPPAlgorithm) (k D G : ℕ):=old source a k D G (ColdOracle.lengthSlot source k)
def gateSlot (a : PointwisePCPPAlgorithm) (k D G : ℕ):=
  old source a k D G (GuardedOracle.flagSlot (ColdOracle.base source k))
def flagSlot (a : PointwisePCPPAlgorithm) (k D G : ℕ):=slots source a k D G (NativePipeline.flagSlot a D G)
def first (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G : ℕ) (code : List Bool):=
  ClockJoin.lifted (Equiv.refl (Fin (tapes source a k D G))) (ColdOracle.machine source k CH Cpad cutoff code)
def second (a : PointwisePCPPAlgorithm) (k D G copies : ℕ) (delta : ℚ):=
  NativePipeline.Dock.machine a D G copies delta (fields source k)
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies : ℕ) (delta : ℚ) (code : List Bool):=
  CloseoutRowsGateColdPair.machine (first source a k CH Cpad cutoff D G code) (second source a k D G copies delta)
    (fun scanned=>scanned (gateSlot source a k D G))
def request (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) {n : ℕ}
    (x : BitInput n) (hpad : k+3 ≤ Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  NativeCache.request a (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))
    (SelectedOracle.width source k CH Cpad code (List.ofFn x))
    (SelectedStreams.queries source k CH Cpad code (List.ofFn x))
    (PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad)
    (PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad) x oracle
def passed (k CH Cpad cutoff G : ℕ) (code x raw : List Bool):=
  ColdOracle.passed source k CH Cpad cutoff code x raw &&
    (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code x) (value raw)).any
      (fun oracle=>decide (oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G
        (SelectedOracle.width source k CH Cpad code x)))

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
