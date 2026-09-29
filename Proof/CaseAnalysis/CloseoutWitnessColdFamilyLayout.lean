import Proof.CaseAnalysis.WitnessFamilyFromPolicyRun
import Proof.CaseAnalysis.WitnessLegalLayout

/-! The guarded original source path enters the whole family through the
retained policy. Only the raw family is added as one independent input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=ColdLegal.tapes source a k D G e+1
def old (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (i : Fin (ColdLegal.tapes source a k D G e)):=i.castAdd 1
def rawSlot (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=(0 : Fin 1).natAdd (ColdLegal.tapes source a k D G e)
def lengthSlot (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=
  old source a k D G e (ColdLegal.lengthSlot source a k D G e)
def countSlot (a : PointwisePCPPAlgorithm) (k D G e : ℕ):=
  old source a k D G e (ColdLegal.old source a k D G e (ColdLegal.countSlot source a k D G))
def policy (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (i : Fin (LegalTemplate.tapes e)):=
  old source a k D G e (ColdLegal.slots source a k D G e i)
def guardSlot (a : PointwisePCPPAlgorithm) (k D G e E : ℕ):=
  FamilyCold.Call.old (FamilyCapacity.Call.old E (old source a k D G e (ColdLegal.flagSlot source a k D G e)))
def first (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E den : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool):=
  TapeEmbedding.machine FamilyCold.Call.extra (TapeEmbedding.machine (FamilyCapacity.Call.extra E)
    (TapeEmbedding.machine 1 (ColdLegal.machine source a k CH Cpad cutoff D G copies e den delta code sym)))


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
