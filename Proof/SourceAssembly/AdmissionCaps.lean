import Proof.Rows.Plan
import Proof.SourceAssembly.AdmissionSmall

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.PolynomialSchedule NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutRawRows (sourceChildBound)
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.RepairSource.CloseoutRawRows (symmetric_occurrences_description threshold_occurrences_description)
open NearCubicWires.SupplierEstimator
open NearCubicWires.P1Closure NearCubicWires.RepairOrdinary

noncomputable section

/-! ## 1. Children and the source cache radix `beta` -/

/-! ## 2. The replicated pool and the layout-dependent sizes -/

section

end

/-! ## 3. Header envelope, stream and precision sizes -/

section

end

/-! ## 4. The admitted request's facts, uniformly over the three constructors -/

/-! ## 5. The three class facts -/


end
end NearCubicWires.Admission
