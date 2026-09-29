import Proof.CaseAnalysis.WitnessSelectedOracle

/-! Exact source fields and disjoint retained scalars at the stream join.
The same selected PCP word is consumed directly, without another call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedStreams
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def selectedFields (k : ℕ) : Fin 3→Fin (HierarchySelectedSource.tapes source k):=
  ![HierarchySelectedSource.outputTape source k,
    HierarchySelectedSource.old source k (HierarchySelectedSource.dimension source k
      (DimensionsFromInput.rawR source.degrees.proofLog source.degrees.queries)),
    HierarchySelectedSource.old source k (HierarchySelectedSource.dimension source k
      (DimensionsFromInput.rawQ source.degrees.proofLog source.degrees.queries))]
def selectedBits (k : ℕ) : Fin 2→Fin (HierarchySelectedSource.tapes source k):=
  ![HierarchySelectedSource.old source k (HierarchySelectedSource.dimension source k
      (DimensionsFromInput.bitsR source.degrees.proofLog source.degrees.queries)),
    HierarchySelectedSource.old source k (HierarchySelectedSource.dimension source k
      (DimensionsFromInput.bitsQ source.degrees.proofLog source.degrees.queries))]

def pcp (k CH Cpad : ℕ) (code x : List Bool):=
  source.output (HierarchySelectedSource.request (HierarchyPadding.rawInput k CH Cpad code x))
def queries (k CH Cpad : ℕ) (code x : List Bool):=
  Dimensions.queries source (HierarchyPadding.rawInput k CH Cpad code x).length

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedStreams
