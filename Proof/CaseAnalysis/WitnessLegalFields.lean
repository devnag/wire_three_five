import Proof.CaseAnalysis.WitnessLegalTemplateDock
import Proof.CaseAnalysis.WitnessNativeLayout

/-! The four actual retained fields of the guarded source/cache path are
the direct legal-policy input. The actual V counter stays distinct. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def sourceSlots (a : PointwisePCPPAlgorithm) (k D G : ℕ) (i : Fin (SourcePolicy.tapes D)):=
  ColdNative.slots source a k D G
    (NativePipeline.localSlots a D G (NativePolicy.policySlots a D i))
def localFields (D : ℕ) : Fin 4→Fin (SourcePolicy.tapes D):=
  ![SourcePolicy.coreSlot D,SourcePolicy.q0Slot D,SourcePolicy.countSlots D 38,SourcePolicy.capSlot D]
def fields (a : PointwisePCPPAlgorithm) (k D G : ℕ):=sourceSlots source a k D G ∘ localFields D
def countSlot (a : PointwisePCPPAlgorithm) (k D G : ℕ):=sourceSlots source a k D G (SourcePolicy.countSlots D 40)



end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
