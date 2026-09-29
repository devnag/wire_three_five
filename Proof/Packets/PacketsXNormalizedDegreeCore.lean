import Proof.Assembly.FixedCore
import Proof.CaseAnalysis.FinalPrinterMonomials

/-! Actual degree certificates through every normalized constructor. The degree
includes the graded-coordinate factor, as required by paper A.10 and A.13. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option linter.unusedVariables false
open NearCubicWires NearCubicWires.RepairSource
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierRadix
open CloseoutRawRows (structuralListCoordinateRawDegree structuralListCoordinateRawDegreeFrom)
namespace PCJ9eff70d512234a4c_Fixed.Normalized
noncomputable section





end
end PCJ9eff70d512234a4c_Fixed.Normalized
