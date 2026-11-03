import Proof.CaseAnalysis.RowsRawMonomialReturn
import Proof.MachineModel.Runs

/-! Literal ports of raw polynomial multiplication. A left monomial is
read with its cursor returned; a right monomial is consumed once. Only the
three actual raw streams and one paid rewind log participate. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductFields
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mark (bit advance : Bool) : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,![none,none,some bit,none],
    ![.stay,if advance then .right else .stay,.right,.stay]⟩ else none

def leftSlots : Fin 3→Fin 4:=![0,2,3]
def rightSlots : Fin 2→Fin 4:=![1,2]
noncomputable def leftMachine:=RecoveryFocus.machine leftSlots CloseoutRowsRawMonomialReturn.machine
noncomputable def rightMachine:=RecoveryFocus.machine rightSlots CloseoutRowsRawMonomialCopy.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductFields
