import Proof.CaseAnalysis.WitnessSelectedNodes
import Proof.PCP.PCPPNativeClauseDescriptorSource

/-! Original x and the same raw oracle reach one faithful pointwise-PCPP
call and its allocated reusable cache. The actual padded request arity is
already retained at public cache slot13/head1 for family circuit validation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad G : ℕ) (code : List Bool):=
  PCPPNativeClauseDescriptorConsumer.sourceMachine a (SelectedNodes.machine source k CH Cpad G code)
    (SelectedNodes.slots source k G 102) (SelectedNodes.widthSlot source k G)
    (SelectedNodes.slots source k G 16) (SelectedNodes.slots source k G 14)
def cacheSlots (a : PointwisePCPPAlgorithm) (k G : ℕ) (j : Fin (PCPPSourceCache.tapes a)):=
  PCPPNativeClauseDescriptorConsumer.cacheSlots a (SelectedNodes.widthSlot source k G)
    (SelectedNodes.slots source k G 16) (SelectedNodes.slots source k G 14) j

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
