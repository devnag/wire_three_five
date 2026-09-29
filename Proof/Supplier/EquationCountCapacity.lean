import Proof.Supplier.EquationCountCopies

/-! The paid row-capacity caller: actual parsed counts produce the doubled
gate header value and C=128*(2d+1)*(p+1), retaining all earlier cut drivers. -/
namespace NearCubicWires.RepairOrdinary.EquationCountCapacity
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


def slots1 : Fin 2 → Fin 32 := ![16,17]
noncomputable def phase1 := RecoveryFocus.machine slots1 (HierarchyFixedWord.machine [false])
def slots2 : Fin 4 → Fin 32 := ![2,16,18,19]
noncomputable def phase2 := RecoveryFocus.machine slots2 (EquationWeightCount.machine)
def slots3 : Fin 3 → Fin 32 := ![18,20,21]
noncomputable def phase3 := RecoveryFocus.machine slots3 (UWalkUnary.machine false false)
def slots4 : Fin 4 → Fin 32 := ![0,16,22,23]
noncomputable def phase4 := RecoveryFocus.machine slots4 (EquationWeightCount.machine)
def slots5 : Fin 3 → Fin 32 := ![22,24,25]
noncomputable def phase5 := RecoveryFocus.machine slots5 (UWalkUnary.machine false true)
def slots6 : Fin 4 → Fin 32 := ![24,6,26,27]
noncomputable def phase6 := RecoveryFocus.machine slots6 (ClockUnaryProduct.machine)
def slots7 : Fin 2 → Fin 32 := ![28,29]
noncomputable def phase7 := RecoveryFocus.machine slots7 (HierarchyFixedWord.machine (CompareMachine.word 128))
def slots8 : Fin 4 → Fin 32 := ![26,28,30,31]
noncomputable def phase8 := RecoveryFocus.machine slots8 (ClockUnaryProduct.machine)

noncomputable def first2 := Composition.machine phase1 phase2
noncomputable def first3 := Composition.machine first2 phase3
noncomputable def first4 := Composition.machine first3 phase4
noncomputable def first5 := Composition.machine first4 phase5
noncomputable def first6 := Composition.machine first5 phase6
noncomputable def first7 := Composition.machine first6 phase7
noncomputable def machine := Composition.machine first7 phase8


end NearCubicWires.RepairOrdinary.EquationCountCapacity
