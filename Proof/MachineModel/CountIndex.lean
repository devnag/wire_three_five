import Proof.CaseAnalysis.RowsCountBinary

/-! A positive physical incidence counter produces the fixed-width last-row
index. The conversion is paid in the raw monomial count, not table capacity. -/
namespace NearCubicWires.ExtIncidence.CountIndex
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey RepairOrdinary.RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 10) : Fin 15:=i.castAdd 5
def scalarSlots : Fin 5→Fin 15:=![10,5,11,12,13]
def predSlots : Fin 3→Fin 15:=![11,12,14]
noncomputable def count:=RecoveryFocus.machine old MatrixDimensionBinary.resetMachine
noncomputable def scalar:=RecoveryFocus.machine scalarSlots ClockNormalize.machine
noncomputable def pred:=RecoveryFocus.machine predSlots RecoveryListPredecessor.machine
noncomputable def first:=Composition.machine count scalar
noncomputable def machine:=Composition.machine first pred
def budget (w M : ℕ):=16*M^2+72*M+8*w+42

end NearCubicWires.ExtIncidence.CountIndex
