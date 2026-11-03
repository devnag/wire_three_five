import Proof.CaseAnalysis.RowsRawPairCopy
import Proof.CaseAnalysis.RowsRawPairSeek

/-! One occurrence block reads the actual adjacent X/C entries from the
source-produced cache and emits their raw sum. Both cache entries are used
without column-dependent syntax or an additional cache representation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPairRead
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawPolynomialAdd
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seekSlots : Fin 2→Fin 5:=![0,1]
noncomputable def seek:=RecoveryFocus.machine seekSlots CloseoutRowsRawPairSeek.machine
noncomputable def machine:=Composition.machine seek CloseoutRowsRawPairCopy.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsRawPairRead
