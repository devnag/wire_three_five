import Proof.CaseAnalysis.WitnessFamilyLift
import Proof.CaseAnalysis.WitnessLegalCacheFields

/-! The actual query-cache ports survive the family alias map. Only its
existing domain13 is shared with the family; the rest are outside it. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

namespace FamilyFromPolicy
end FamilyFromPolicy

namespace ColdLegal
end ColdLegal

namespace ColdFamily
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def cache (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) (j : Fin 19):=
  ColdFamilyLift.old E (ColdLegal.cache source a k D G e j)

end ColdFamily

end
end NearCubicWires.RepairOrdinary.CloseoutWitness
