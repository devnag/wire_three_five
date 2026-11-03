import Proof.CaseAnalysis.RowsModeCacheHash
import Proof.CaseAnalysis.RowsModeCacheSource
import Proof.Supplier.EquationZeroField
import Proof.Supplier.RowThresholdSelections

/-! Repeated cache passes retain original inputs and the last child count.
Private backing is erased at the next entry, before the actual source runs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reuseEraseSlots : Fin 17→Fin 28:=![1,4,6,7,8,10,13,14,15,16,17,18,19,22,23,26,27]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
