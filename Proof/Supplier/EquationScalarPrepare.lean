import Proof.Supplier.EquationScalarWiden

/-! Cold signed-field preparation: physically save its sign, initialize
the scalar flags and isolate one-bit-wider magnitude. Every head is reset
from the executed prefix; no width or workspace is supplied separately. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar.Prepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section


def bootstrap : Machine 10 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bs => if q.val=0 then
      some ⟨1,fun i => if i=4 ∨ i=7 then some false else none,
        fun i => if i=0 then .right else .stay⟩
    else if q.val=1 then
      some ⟨2,fun i => if i=1 then some (bs 0) else none,
        fun i => if i=0 then .right else .stay⟩
    else none

def slots : Fin 2→Fin 10 := ![0,2]
def widen := RecoveryFocus.machine slots EquationWiden.machine
def raw := Composition.machine bootstrap widen
def machine := TapeEmbedding.machine 1 (Rewind.machine raw)

end
end NearCubicWires.RepairOrdinary.EquationScalar.Prepare
