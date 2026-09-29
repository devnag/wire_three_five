import Proof.Supplier.EquationRowRaw

/-! The complete raw row producer has a fixed cubic parameter envelope,
plus its single linear scan of the actual original word. -/
namespace NearCubicWires.RepairOrdinary.EquationRowRaw
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mass (r : EquationRow.Input) := r.d+r.p+r.cuts.length+1

end NearCubicWires.RepairOrdinary.EquationRowRaw
