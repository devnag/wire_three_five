import Proof.Supplier.EquationScalarScan

/-! Physically prepend the canonical sign to the prepared magnitude,
copy its complete frame, and rewind every local head. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar.Emit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def negative (negate sign nonzero : Bool) : Bool := (if negate then !sign else sign) && nonzero

def bootstrap (negate : Bool) : Machine 4 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bs => if q.val=0 then
      some ⟨1,![none,none,none,some true],![.stay,.stay,.stay,.right]⟩
    else if q.val=1 then
      some ⟨2,![none,none,none,some (negative negate (bs 1) (bs 2))],![.stay,.stay,.stay,.right]⟩
    else none

def slots : Fin 2→Fin 4 := ![0,3]
def copy := RecoveryFocus.machine slots Field.machine
def raw (negate : Bool) := Composition.machine (bootstrap negate) copy
def machine (negate : Bool) := Rewind.machine (raw negate)

end
end NearCubicWires.RepairOrdinary.EquationScalar.Emit
