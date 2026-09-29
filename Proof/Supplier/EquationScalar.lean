import Proof.Supplier.EquationScalarGraph

/-! Cold signed successor and negation for the literal matrix scalar codec.
The opcode is static; both width and sign are read from the actual field. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def machine (negate : Bool) := Graph.machine negate

end
end NearCubicWires.RepairOrdinary.EquationScalar
