import Proof.Hierarchy.CompetitorCountProducer
import Proof.MachineModel.ClockFields

/-! Execute the exact paper normalization denominator. The first count is
the prime-list cardinality for THR and one for SYM; it never counts child
tuples. The binary power of two is physically printed from the unary q word,
then two short multiplications produce P * E * 2^q. All work starts blank. -/
namespace NearCubicWires.RepairOrdinary.CompetitorDenominator
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def powerBits (q : ℕ) := List.replicate q false++[true]
def powerSlots : Fin 6 → Fin 37 := ![3,4,5,6,7,8]
def firstSlots (j : Fin 14) : Fin 37 :=
  if j.val=0 then 0 else if j.val=8 then 1 else if j.val=9 then 2
  else ⟨9+j.val,by omega⟩
def secondSlots (j : Fin 14) : Fin 37 :=
  if j.val=0 then 4 else if j.val=8 then 12 else if j.val=9 then 2
  else ⟨23+j.val,by omega⟩
noncomputable def powerProgram := RecoveryFocus.machine powerSlots ClockFields.machine
noncomputable def firstProgram := RecoveryFocus.machine firstSlots HierarchyMultiplyEntry.machine
noncomputable def secondProgram := RecoveryFocus.machine secondSlots HierarchyMultiplyEntry.machine
noncomputable def machine := Composition.machine powerProgram (Composition.machine firstProgram secondProgram)
def budget (b w q : ℕ) := 4*q+24+128*(w+1)*(b+q+3)

theorem power_value (q : ℕ) : value (powerBits q)=2^q := by
  simp [powerBits,value_append,ClockScalarFields.zeros_value,value]

end NearCubicWires.RepairOrdinary.CompetitorDenominator
