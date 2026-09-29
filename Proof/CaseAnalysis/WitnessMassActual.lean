import Proof.CaseAnalysis.WitnessMassReusableCheck
import Proof.CaseAnalysis.MassThresholdWidth

/-! The actual unchanged paper mass cap fits every produced witness policy.
Its complete ordinary check has no additional size guard or cutoff premise. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassActual
open LocalBitMultitape CompetitorSumFold
open CompetitorValidity (Estimate)
open RepairSource CloseoutMassThreshold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassActual
