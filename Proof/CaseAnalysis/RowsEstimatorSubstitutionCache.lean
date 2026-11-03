import Proof.CaseAnalysis.RowsRawPairReusable

/-! The shared Pair cache supplies an atom at head zero, beside the live source cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionCache
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine CloseoutRowsRawPairReusable.machine (fun i=>decide (i=2))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionCache
