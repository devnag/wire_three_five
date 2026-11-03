import Proof.CaseAnalysis.WitnessSourcePolicyCall

/-! Original input and the same raw oracle reach the faithful PCPP source
and its one-time family policy. The entire source cache survives unchanged;
no source word, metadata counter or coefficient template is supplied free. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedPolicy
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces
open VerifierDecoding CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem fields_joined (D copies : ℕ) (delta : ℚ) {t n0 s z : ℕ} (fields : Fin 2→Fin t)
    (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (first : ExecutionReceipt (t+SourcePolicy.Call.extra D) s)
    (last : ExecutionReceipt (t+SourcePolicy.Call.extra D) z)
    (h : SourcePolicy.Call.Fields D copies delta fields r p last.final) :
    SourcePolicy.Call.Fields D copies delta fields r p (Composition.joinedReceipt first last).final:=
  ⟨h.count,h.clause,h.q0,h.cap,h.cursor⟩

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (a : PointwisePCPPAlgorithm) (k G : ℕ):=
  PCPPNativeSource.tapes a (PCPPNativeClauseDescriptorConsumer.tapes (SelectedNodes.tapes source k G))
def fields (a : PointwisePCPPAlgorithm) (k G : ℕ) : Fin 2→Fin (base source a k G):=
  ![SelectedSource.cacheSlots source a k G (PCPPSourceCache.cacheSlots a 0),
    SelectedSource.cacheSlots source a k G (PCPPSourceCache.cacheSlots a 13)]
def first (a : PointwisePCPPAlgorithm) (k CH Cpad G D : ℕ) (code : List Bool):=
  TapeEmbedding.machine (SourcePolicy.Call.extra D) (SelectedSource.machine source a k CH Cpad G code)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedPolicy
