import Proof.MachineModel.UWalkUnary
import Proof.Supplier.EquationWeightCount

/-! The actual parsed d/p/G/odd bank supplies all cut-loop counts and the
first two output-header values. Every copy and physical rewind is paid. -/
namespace NearCubicWires.RepairOrdinary.EquationCountCopies
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots1 : Fin 4 → Fin 16 := ![0,3,4,5]
noncomputable def phase1 := RecoveryFocus.machine slots1 (EquationWeightCount.machine)
def slots2 : Fin 3 → Fin 16 := ![1,6,7]
noncomputable def phase2 := RecoveryFocus.machine slots2 (UWalkUnary.machine true true)
def slots3 : Fin 3 → Fin 16 := ![6,8,9]
noncomputable def phase3 := RecoveryFocus.machine slots3 (UWalkUnary.machine true true)
def slots4 : Fin 3 → Fin 16 := ![2,10,11]
noncomputable def phase4 := RecoveryFocus.machine slots4 (UWalkUnary.machine true false)
def slots5 : Fin 3 → Fin 16 := ![0,12,13]
noncomputable def phase5 := RecoveryFocus.machine slots5 (UWalkUnary.machine false false)
def slots6 : Fin 3 → Fin 16 := ![1,14,15]
noncomputable def phase6 := RecoveryFocus.machine slots6 (UWalkUnary.machine false true)

noncomputable def first2 := Composition.machine phase1 phase2
noncomputable def first3 := Composition.machine first2 phase3
noncomputable def first4 := Composition.machine first3 phase4
noncomputable def first5 := Composition.machine first4 phase5
noncomputable def machine := Composition.machine first5 phase6

end NearCubicWires.RepairOrdinary.EquationCountCopies
