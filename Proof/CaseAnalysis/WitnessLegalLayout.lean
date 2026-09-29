import Proof.CaseAnalysis.WitnessLegalFields
import Proof.CaseAnalysis.RowsCircuitGuarded

/-! One size-guarded native source path enters the legal-family policy.
The actual source-derived q0/clause/width and retained cache are aliased. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def tapes (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=ColdNative.tapes source a k D G+LegalTemplate.Call.extra e
def old (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (i : Fin (ColdNative.tapes source a k D G)):=LegalTemplate.Call.old e i
def slots (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=LegalTemplate.Call.slots e (fields source a k D G)
def flagSlot (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=old source a k D G e (ColdNative.flagSlot source a k D G)
def lengthSlot (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=old source a k D G e (ColdNative.lengthSlot source a k D G)
def first (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e : ℕ) (delta : ℚ) (code : List Bool):=
  TapeEmbedding.machine (LegalTemplate.Call.extra e) (ColdNative.machine source a k CH Cpad cutoff D G copies delta code)
def second (a : PointwisePCPPAlgorithm) (k D G e den copies : ℕ) (delta : ℚ) (sym : Bool):=
  LegalTemplate.Call.machine e den delta copies sym (fields source a k D G)
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e den : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool):=
  CloseoutRowsGateColdPair.machine (first source a k CH Cpad cutoff D G copies e delta code)
    (second source a k D G e den copies delta sym) (fun scanned=>scanned (flagSlot source a k D G e))

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
