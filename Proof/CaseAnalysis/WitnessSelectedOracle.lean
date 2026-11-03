import Proof.CaseAnalysis.WitnessOracleCallRun
import Proof.Hierarchy.HierarchySelectedSource
import Proof.PCP.ProjectionDimensionCanonical

/-! Original input and raw oracle guess through the one selected PCP call,
then the cold oracle decoder. The exact source bank survives for the native
PCPP continuation, so neither the hierarchy nor the source is run twice. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedOracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=HierarchySelectedSource.tapes source k
abbrev tapes (k : ℕ):=OracleCall.tapes (base source k)
def old (k : ℕ) : Fin (base source k)→Fin (tapes source k):=OracleCall.old
def fields (k : ℕ) : Fin 3→Fin (base source k):=
  ![HierarchySelectedSource.old source k
      (HierarchyPrefix.old k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source)
        (HierarchyFramedInput.old k (HierarchyReduction.xTape k))),
    HierarchySelectedSource.old source k
      (HierarchySelectedSource.dimension source k (DimensionsFromInput.bitsR
        (HierarchySelectedSource.p source) (HierarchySelectedSource.q source))),
    HierarchySelectedSource.old source k
      (HierarchySelectedSource.dimension source k (DimensionsFromInput.rawR
        (HierarchySelectedSource.p source) (HierarchySelectedSource.q source)))]
def width (k CH Cpad : ℕ) (code x : List Bool):=
  Dimensions.width source (HierarchyPadding.rawInput k CH Cpad code x).length
def first (k CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (old source k) (HierarchySelectedSource.machine source k CH Cpad code)
def second (k : ℕ):=OracleCall.machine (fields source k)
def machine (k CH Cpad : ℕ) (code : List Bool):=Composition.machine (first source k CH Cpad code) (second source k)
def descriptorSlot (k : ℕ):=OracleCall.parserSlots (base source k) Oracle.descriptorSlot

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedOracle
