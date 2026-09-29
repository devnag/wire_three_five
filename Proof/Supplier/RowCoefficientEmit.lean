import Proof.Supplier.RowCoefficientNormalize

/-! The physical nonnegative flag and framed absolute magnitude produce the
ordinary sign/magnitude field. Both sign writes, every magnitude bit, and
the final head reset are executed by this fixed four-tape program. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientEmit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==3
  rule := fun q bits=>if q.val=0 then some
    ⟨if bits 0 then 1 else 2,![none,none,some true],![.stay,.stay,.right]⟩
    else if q.val=1 ∨ q.val=2 then some
      ⟨3,![none,none,some (q.val==2)],![.stay,.stay,.right]⟩ else none
def slots : Fin 2 → Fin 3 := ![1,2]
noncomputable def copy := RecoveryFocus.machine slots Field.machine
noncomputable def raw := Composition.machine boot copy
noncomputable def machine := Rewind.machine raw

end NearCubicWires.RepairOrdinary.RowCoefficientEmit
