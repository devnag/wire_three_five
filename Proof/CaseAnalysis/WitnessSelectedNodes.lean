import Proof.CaseAnalysis.WitnessSelectedCap
import Proof.CaseAnalysis.WitnessNativeNodeCall
import Proof.PCP.PCPPNativeHierarchyNodesCircuit

/-! Original input and the same decoded oracle emit the actual compact
substituted DAG after the paid exact cap test. No native descriptor or metadata
is supplied, and neither source selection nor counter production is repeated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedNodes
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k G : ℕ):=SelectedCap.tapes source k G
abbrev tapes (k G : ℕ):=base source k G+363
def counter (k G : ℕ):=SelectedCap.slots source k G
def slots (k G : ℕ):=NativeNodeCall.slots (counter source k G)
def widthSlot (k G : ℕ):=NativeNodeCall.old (counter source k G 72)
def first (k CH Cpad G : ℕ) (code : List Bool):=
  TapeEmbedding.machine 363 (SelectedCap.machine source k CH Cpad G code)
def second (k G : ℕ):=NativeNodeCall.machine (counter source k G)
def machine (k CH Cpad G : ℕ) (code : List Bool):=
  Composition.machine (first source k CH Cpad G code) (second source k G)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedNodes
