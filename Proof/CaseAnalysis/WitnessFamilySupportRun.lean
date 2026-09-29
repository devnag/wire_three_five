import Proof.CaseAnalysis.WitnessFamilySupportFromPolicyRun
import Proof.CaseAnalysis.WitnessFamilySupportSupplier

/-! The original cold source and policy enter the actual strengthened
family. All inputs, including rejected branches, use twice the old fuel;
the new support stream is retained only after the same old verdict passes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilySupport
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization CanonicalWitnessCodec
open CompetitorSumFold CompetitorSumWidth RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def actualMachine (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E K den km : ℕ)
    (delta q : ℚ) (code : List Bool) (sym : Bool):=
  machine source (FamilySupport.Actual sym km q) a k CH Cpad cutoff D G copies e E K den delta code sym

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilySupport
