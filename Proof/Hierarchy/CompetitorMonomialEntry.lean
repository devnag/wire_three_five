import Proof.Hierarchy.CompetitorMonomialColdClear

/-! Whole bulk monomial producer from blank work tapes and physical record,
width/capacity/count inputs. One paid outer rewind resets both global
cursors only after the entire stream has been emitted. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding CompetitorMonomialStream CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outerSlots (j : Fin 88) : Fin 89 := j.castAdd 1
def extendTapes (tapes : Fin 88 → List Bool) (n : ℕ) : Fin 89 → List Bool :=
  Fin.addCases (m := 88) (n := 1) (motive := fun _ => List Bool) tapes (fun _ => CompareMachine.word n)
noncomputable def bootProgram := RecoveryFocus.machine outerSlots (clearProgram workSlot)
def enter : Machine 89 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i.val=88 then .right else .stay⟩ else none
noncomputable def tailProgram := Composition.machine enter loopProgram
noncomputable def program := Composition.machine bootProgram tailProgram
def budget (t n : ℕ) := loopBudget t n+2*capacity t+7

noncomputable def machine := Rewind.machine program
def readyBudget (t n : ℕ) := 2*budget t n+2

end NearCubicWires.RepairOrdinary.CompetitorMonomialEntry
