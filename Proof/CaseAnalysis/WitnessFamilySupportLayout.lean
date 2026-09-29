import Proof.CaseAnalysis.WitnessFamilyOuterBudget
import Proof.CaseAnalysis.WitnessFamilySupportPrefix
import Proof.CaseAnalysis.WitnessFamilyCacheFields

/-! The pinned support-family continuation enters the original cold source
bank with one final tape. Every original family/cache address keeps its value. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilySupport
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def cache (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) (j : Fin 19):=
  (ColdFamily.cache source a k D G e E j).castAdd 1
def guardSlot (a : PointwisePCPPAlgorithm) (k D G e E : ℕ):=
  (ColdFamily.guardSlot source a k D G e E).castAdd 1
def first (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E den : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool):=
  TapeEmbedding.machine 1 (ColdFamily.first source a k CH Cpad cutoff D G copies e E den delta code sym)
def second {s : ℕ} (supplier : Machine 3244 s) (a : PointwisePCPPAlgorithm) (k D G e E K : ℕ):=
  FamilySupportFromPolicy.machine supplier e E K (ColdFamily.lengthSlot source a k D G e)
    (ColdFamily.countSlot source a k D G e) (ColdFamily.rawSlot source a k D G e) (ColdFamily.policy source a k D G e)
def machine {s : ℕ} (supplier : Machine 3244 s) (a : PointwisePCPPAlgorithm)
    (k CH Cpad cutoff D G copies e E K den : ℕ) (delta : ℚ) (code : List Bool) (sym : Bool):=
  CloseoutRowsGateColdPair.machine (first source a k CH Cpad cutoff D G copies e E den delta code sym)
    (second source supplier a k D G e E K) (fun scanned=>scanned (guardSlot source a k D G e E))


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilySupport
