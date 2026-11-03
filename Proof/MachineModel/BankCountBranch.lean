import Proof.MachineModel.BankCountPositive
import Proof.MachineModel.BankCountZero

/-! Dispatch on the original raw stream marker in the same count bank. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def idle : Machine 128 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def dispatch {s t : ℕ} (yes : Machine 128 s) (no : Machine 128 t):=
  CloseoutWitness.HeaderSwitch.machine idle yes no (fun _=>true) (fun cells=>cells 113)
def optional:=dispatch positive zero

end
end NearCubicWires.ExtIncidence.BankCount
