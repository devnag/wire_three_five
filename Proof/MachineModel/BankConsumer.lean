import Proof.MachineModel.BankExecution
import Proof.MachineModel.BankFields

/-! Physical raw incidence production, paid cursor return, and the EXISTING
polynomial consumer. All other native fields are explicit caller-produced
inputs. The separate zero-polynomial branch is not supplied here. -/
namespace NearCubicWires.ExtIncidence.BankConsumer
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 113) : Fin 116 := i.castAdd 3

noncomputable def consumer:=RecoveryFocus.machine old CloseoutRowsBankPolynomial.machine
noncomputable def machine:=Composition.machine BankExecution.machine consumer
def budget (B C Q : ℕ) (ms : List (List ℕ)):=
  BankExecution.budget B C ms+1+CloseoutRowsBankPolynomial.budget Q C

end NearCubicWires.ExtIncidence.BankConsumer
