import Proof.CaseAnalysis.RowsRawProductLoop

/-! Raw polynomial addition uses the checked row writer with the empty
left monomial. Each original polynomial is scanned once; neither duplicate
monomials nor repeated variable occurrences are cancelled. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPolynomialAdd
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftSlots : Fin 4→Fin 5:=![3,0,2,4]
def rightSlots : Fin 4→Fin 5:=![3,1,2,4]
noncomputable def leftMachine:=RecoveryFocus.machine leftSlots CloseoutRowsRawProductRow.machine
noncomputable def rightMachine:=RecoveryFocus.machine rightSlots CloseoutRowsRawProductRow.machine
def finish : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,![none,none,some false,none,none],
    ![.stay,.stay,.right,.stay,.stay]⟩ else none
noncomputable def machine:=Composition.machine (Composition.machine leftMachine rightMachine) finish

end NearCubicWires.RepairOrdinary.CloseoutRowsRawPolynomialAdd
