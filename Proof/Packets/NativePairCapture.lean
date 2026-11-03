import Proof.CaseAnalysis.RowsRawPairCopy
import Proof.Rows.PhysicalFocusBoundary

/-! Copy the two actually resident polynomial halves of an atom pair to one
native stream, and pay for returning that stream cursor to zero. The pair
cache cursor advances, all work backing is reusable, and no result stream
is supplied as a machine parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativePairCapture
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair word)

def selected (i : Fin 5) := decide (i=2)
noncomputable def machine := MaskedReset.machine CloseoutRowsRawPairCopy.machine selected

end PCJ9eff70d512234a4c_Fixed.Materializer.NativePairCapture
