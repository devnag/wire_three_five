import Proof.CaseAnalysis.FinalSupplierCalls
import Proof.CaseAnalysis.RowsEstimatorCoefficientsPrepare
import Proof.CaseAnalysis.RowsEstimatorCoefficientsProductRead

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceFactorSel.CoefValue
open NearCubicWires RepairOrdinary

/-- Per-slot unary quantities (magnitude, denominator, sign count). -/
def nA (f : Bool) (t : ℚ) : ℕ := if f then t.num.natAbs else 1
def dA (f : Bool) (t : ℚ) : ℕ := if f then t.den else 1
def sA (f : Bool) (t : ℚ) : ℕ := if f then (decide (t.num < 0)).toNat else 0


end NearCubicWires.SourceFactorSel.CoefValue

