import Proof.Supplier.EquationRowForward
import Proof.Assembly.AppendOutputFrame

/-! A complete fixed ordinary machine reads the original equation row and
emits the exact externally framed matrix request, with every head reset. -/
namespace NearCubicWires.RepairOrdinary.EquationRowFramed
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := AppendOutputFrame.machine EquationRowRaw.machine 110
def input (r : EquationRow.Input) : Fin 130 → List Bool :=
  fun i => if i=0 then frame (EquationRowRaw.source r) else []

end NearCubicWires.RepairOrdinary.EquationRowFramed
