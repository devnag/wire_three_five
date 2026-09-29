import Proof.Hierarchy.CompetitorSumBootstrap

/-! Whole cold ordinary signed-rational fold. Only the scalar-record stream
and its physical dimension words are supplied; all work tapes start blank
and every head starts at zero. The initialization, entry, updates, driver
exhaustion and reset are all in the stated execution budget. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding CompetitorSumFold CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outerSlots (j : Fin 94) : Fin 95 := j.castAdd 1
def extendTapes (tapes : Fin 94 → List Bool) (n : ℕ) : Fin 95 → List Bool :=
  Fin.addCases (m := 94) (n := 1) (motive := fun _ => List Bool) tapes (fun _ => CompareMachine.word n)
def input (b : ℕ) (xs : List CompetitorValidity.Estimate) := extendTapes (coldInput b (words b xs)) xs.length
noncomputable def bootProgram := RecoveryFocus.machine outerSlots bootstrapProgram
def enter : Machine 95 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i.val=94 then .right else .stay⟩ else none
noncomputable def tailProgram := Composition.machine enter loopProgram
noncomputable def machine := Composition.machine bootProgram tailProgram
def budget (b n : ℕ) := loopBudget b n+2*capacity b+20*b+61

end NearCubicWires.RepairOrdinary.CompetitorSumEntry
