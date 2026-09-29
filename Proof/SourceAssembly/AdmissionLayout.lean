import Proof.Assembly.RowAdapter
import Proof.CaseAnalysis.FinalModeNativeEnvelope
import Proof.CaseAnalysis.FiveLiveSetCaps

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierPrime
open NearCubicWires.PolynomialSchedule NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open NearCubicWires.RepairOrdinary.CloseoutRowsRawLogShape
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RepairSource.CloseoutRawRows (descriptionEnvelope descriptionEnvelope_polynomial
  actual_description_envelope symmetric_occurrences_description threshold_occurrences_description
  polynomial_walk_log polynomial_bits_log wire_le_cube bits_two_pow rowDepthAt windowSumAt)
open PCJ9eff70d512234a4c_Fixed

noncomputable section

/-! ## 1. The carried cap is at most cubic -/

/-! ## 2. Descriptions of the native circuits -/

/-! ## 3. The child alphabet is `2^{O(L_q)}` -/

/-! ## 4. The THR prime-digit and walk factors are `O(L_q)` -/

/-! ## 5. Layout existence -/


end
end NearCubicWires.Admission
