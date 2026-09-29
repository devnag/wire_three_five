import Proof.Wire_3_5.Recovery.HybridProgSourceRun

/-! # The hybrid `E^NP` program: SourceBounds (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramSourceBounds`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: One source-selected capacity pays every native recovery request and the resulting full recovery budget. All coefficients are fixed in advance.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
open SelectedRecoveryIntegration RecoveryScheduleEnvelope BoundedOracleStructuralCircuit
set_option autoImplicit false
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
end NearCubicWires.RepairSource.HybridProgram
