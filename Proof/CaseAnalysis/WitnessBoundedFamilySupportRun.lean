import Proof.CaseAnalysis.WitnessBoundedFamilySupportLayout
import Proof.CaseAnalysis.WitnessFamilySupportRun

/-! One bounded header runs exactly one actual strengthened cold family.
The enclosing receipt retains every selected child field, so subsequent
row consumers use this same source call and its original cache. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamilySupport
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def actualMachine (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies E K symDen thrDen km : ℕ)
    (delta q : ℚ) (code : List Bool):=
  machine source (fun sym=>⟨_,FamilySupport.Actual sym km q⟩) a k CH Cpad cutoff D G copies E K symDen thrDen delta code

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamilySupport
