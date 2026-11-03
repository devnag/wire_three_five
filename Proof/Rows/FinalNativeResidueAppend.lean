import Proof.Rows.FinalNativeResidue
import Proof.CaseAnalysis.RowsTouchingFrameStream

/-! One physical native signed coefficient is reduced and appended in the
actual modular row's framed summand grammar. The original source cursor is
retained; this does not clear the scalar workspace for the next coefficient. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueAppend
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


def budget (negate : Bool) (z : ℤ) (w : ℕ) := C10NativeResidue.budget negate z w+1+(2*w+1)

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueAppend
