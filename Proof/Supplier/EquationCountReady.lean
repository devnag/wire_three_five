import Proof.Supplier.EquationCountCapacity

/-! The complete count/capacity bank is produced from d,p,G,odd alone.
No output count, scalar width or erase capacity is supplied to this caller. -/
namespace NearCubicWires.RepairOrdinary.EquationCountReady
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 16) : Fin 32 := i.castAdd 16
noncomputable def first := RecoveryFocus.machine slots EquationCountCopies.machine
noncomputable def machine := Composition.machine first EquationCountCapacity.machine

end NearCubicWires.RepairOrdinary.EquationCountReady
