import Proof.MachineModel.ClockFields
import Proof.Supplier.RowCoefficientEmit

/-! A fixed unary scan computes the binLift degree sign. It returns the
degree word and the sign with both heads reset, paying its recording tape. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeSign
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def positive : ℕ → Bool
  | 0 => true
  | j+1 => !(positive j)
def raw : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=2 then none else some
    (if bits 0 then ⟨if q.val=0 then 1 else 0,![none,none],![.right,.stay]⟩
     else ⟨2,![none,some (q.val==0)],![.stay,.stay]⟩)
def machine := Rewind.machine raw
def input (j : ℕ) : Fin 3 → List Bool := ![List.replicate j true,[],[]]

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeSign
