import Proof.CaseAnalysis.RowsModeLiteralSelect

/-! Fixed physical cache population layout. The original mask, seed and
level are retained; the actual label and two distinct live counts advance. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true





def guardSlots : Fin 6→Fin 24:=![8,12,13,14,15,10]
def selectSlots : Fin 7→Fin 24:=![13,14,15,11,16,17,23]
def pairSlots : Fin 5→Fin 24:=![16,18,20,19,17]
def labelSlots : Fin 2→Fin 24:=![1,10]
def eraseSlots : Fin 5→Fin 24:=![4,6,8,21,22]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
