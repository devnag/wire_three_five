import Proof.Supplier.EquationRowFramed
import Proof.Supplier.EquationRowBounds

/-! The composable ordinary row-to-matrix supplier with a uniform proved
budget and physical reset. No local execution record is an input premise. -/
namespace NearCubicWires.RepairOrdinary.EquationRowFramed
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def uniformBudget (r : EquationRow.Input) :=
  600000*(EquationRowRaw.mass r)^3+24*(EquationRowRaw.source r).length+7

end NearCubicWires.RepairOrdinary.EquationRowFramed
