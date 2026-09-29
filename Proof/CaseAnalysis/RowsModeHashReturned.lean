import Proof.CaseAnalysis.RowsModeHashMeaning

/-! Return the three forward-scanned heads after one actual Toeplitz bit.
The original seed words are retained, and the translation cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashReturned
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsModeHashBit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 7):=decide (i=0∨i=1∨i=3)
def machine:=MaskedReset.machine CloseoutRowsModeHashBit.machine selected

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashReturned
