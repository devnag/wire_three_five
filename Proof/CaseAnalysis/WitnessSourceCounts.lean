import Proof.CaseAnalysis.WitnessSourceFields
import Proof.CaseAnalysis.CapacityPower

/-! Actual source metadata supplies the exact distinct-variable count V
and actual clause-bit driver. All template copies and the V sum are paid;
the same PCPP output is retained without any source serialization. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SourceCounts
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 34) : Fin 42:=i.castAdd 8
def copySlots : Fin 3→Fin 3→Fin 42:=![![10,34,35],![20,36,37],![30,38,39]]
def sumSlots : Fin 4→Fin 42:=![34,36,40,41]
noncomputable def field:=RecoveryFocus.machine old SourceFields.machine
noncomputable def copy (i : Fin 3):=RecoveryFocus.machine (copySlots i) (UWalkUnary.machine false false)
noncomputable def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def first:=Composition.machine field (copy 0)
noncomputable def second:=Composition.machine first (copy 1)
noncomputable def third:=Composition.machine second (copy 2)
noncomputable def machine:=Composition.machine third sum
def budget (a b c : ℕ):=
  SourceFields.budget a b c+1+(2*a+6)+1+(2*b+6)+1+(2*c+6)+1+(2*(a+b)+6)


end NearCubicWires.RepairOrdinary.CloseoutWitness.SourceCounts
