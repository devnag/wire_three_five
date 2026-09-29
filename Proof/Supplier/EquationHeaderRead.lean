import Proof.MachineModel.OrdinaryMatrixCoefficientHeaders

/-! The same cold three-header parser, specialized to a generic equation
stream suffix. No weak-cut Request or prepared unary dimension is needed. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaderRead
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def header (d p g : ℕ) := natWord d++natWord p++natWord g
def word (d p g : ℕ) (suffix : List Bool) := header d p g++suffix
noncomputable def machine := MatrixCoefficientHeaders.machine

end NearCubicWires.RepairOrdinary.EquationHeaderRead
