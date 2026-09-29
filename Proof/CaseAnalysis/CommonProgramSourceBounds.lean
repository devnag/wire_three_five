import Proof.CaseAnalysis.CommonProgramSourceRun

/-! One source-selected capacity pays every native recovery request and
the resulting full recovery budget. All coefficients are fixed in advance. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
open SelectedRecoveryIntegration RecoveryScheduleEnvelope BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem recovery_description (p : Parameters) (r : InputRequest)
    (small : RecoveryChoice.SmallOracle (globalPCP p) p.degree r.2) :
    recoveryDescription p r=frame (CanonicalSATSelfReduction.recoveredPrefix
      (BoundedOracleStructuralCircuit.descriptionWidth (R p r) (B p r))
      (boundedOracleRecoveryFormula (globalPCP p) r.2 (B p r))):=by
  apply congrArg frame
  exact (RecoveryBoundedCold.description_hierarchy (source p) (hierarchy p) (pad p)
    (pad_large p) p.degree r small).trans
      (CloseoutCaseTwo.Selected.recovered_description (globalPCP p) p.degree r.2 small).symm

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
