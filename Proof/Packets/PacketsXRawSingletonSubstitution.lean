import Proof.CaseAnalysis.RowsEstimatorSubstitutionMonomial
import Proof.CaseAnalysis.RowsEstimatorSubstitutionOuterRun
import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.Rows.PhysicalFocusBoundary

/-! Reusable raw singleton substitution on a physically allocated bank.
The original executed substitution is followed by a paid reset of every
cursor; its private words already return to the same padded zero backing. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.RawSingletonSubstitution
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (Pair cacheWord)

noncomputable def machine := MaskedReset.machine CloseoutRowsEstimator.SubstitutionOuter.machine (fun _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.RawSingletonSubstitution
