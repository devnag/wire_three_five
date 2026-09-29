import Proof.CaseAnalysis.FinalThresholdParityRow
import Proof.CaseAnalysis.FinalUnionSupplier

/-!
A.13.10: the natural sum of the separate fixed `(g,p,e,f)` table counts.
The scalar offset is selected from the residual column; it is not a vector
of offsets hidden inside a polynomial. The child label stays outside GF(2).
This module supplies local value/error adapters, not a physical supplier run.
Resource owner: A.8 and A.13.8; per-g printing retains the existing row fit.
-/

open NearCubicWires NearCubicWires.RepairSource
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.SupplierPrinter
open NearCubicWires.SupplierWalk NearCubicWires.SupplierRadix
open NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.CloseoutRawRows

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdNaturalSum

open C10PrinterBridge C10ThresholdParityRow

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

open CloseoutFinalC10ThresholdRows

open C10UnionSupplier


end
end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdNaturalSum
