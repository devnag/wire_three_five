import Proof.CaseAnalysis.WitnessFamilyCount
import Proof.CaseAnalysis.WitnessMassActual
import Proof.CaseAnalysis.WitnessMassReusableStep
import Proof.CaseAnalysis.WitnessSumGuard
import Proof.CaseAnalysis.WitnessTermCoefficient

/-! The reusable mass round consumes the coefficient reader's existing
allocated fields. Only its two coefficient operands receive zero padding;
the native store and the paid scratch reset are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassOperands
open LocalBitMultitape RecoveryRootRound SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true



end NearCubicWires.RepairOrdinary.CloseoutWitness.MassOperands
