import Proof.CaseAnalysis.WitnessLegalLayout

/-! The legal-policy input shares only cache domain13; all remaining
prepaid cache tapes lie outside its four retained input fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def cache (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (j : Fin 19):=
  old source a k D G e (ColdNative.cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j))


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
