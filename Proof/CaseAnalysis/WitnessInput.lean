import Proof.CaseAnalysis.WitnessFamilyCacheFields

/-! The complete cold family has exactly three original input tapes.
All other tapes start blank and can be supplied by the existing header's
fresh bank without a copy or a second source execution. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdInput
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def oracleIndex (k : ℕ):=ColdSource.tapes source k+4+1

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdInput
