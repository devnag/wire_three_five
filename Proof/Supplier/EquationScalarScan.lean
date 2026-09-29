import Proof.Circuits.DecompositionBitFields
import Proof.Supplier.EquationScalarWiden

/-! Reuse the accepted Boolean-field scan to decide canonical zero,
including an actual rewind from its cold local bank. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar.Scan
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine := Rewind.machine DecompositionBitFields.machine

end NearCubicWires.RepairOrdinary.EquationScalar.Scan
