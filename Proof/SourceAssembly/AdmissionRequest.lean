import Proof.Assembly.Production
import Proof.SourceAssembly.AdmissionLayout

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalk
open NearCubicWires.PolynomialSchedule NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RepairSource.CloseoutRawRows (descriptionEnvelope descriptionEnvelope_polynomial
  sourceChildBound sourceChildBound_polynomial)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope (seedEnvelope seedEnvelope_le_of_bits
  walkExponent_le_seedEnvelope touchingCost_le_length primesUpTo_card_le)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth (walkExponent card_walkSample)
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production

noncomputable section

/-! ## 1. The admitted runtime request -/

/-! ## 2. Logarithms as polynomials -/

/-! ## 3. The walk-seed count -/

/-! ## 4. `h_rows` -/


end
end NearCubicWires.Admission
