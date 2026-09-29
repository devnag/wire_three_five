import Proof.Amplification.RecoveryRawLiteralBoundMeaning

/-! Bounded literal iteration uses the actual supplied unary driver. Its
body rejects only a missing code cell and retains natural-tag invalidity. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RecoveryRawLiteralBound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def next (x : State) : Bool×State := (decide (code x≠0),output x)
noncomputable def source (x : State) := x.cfg RecoveryRawLiteralBound.machine.start
noncomputable def machine := RepeatMachine.machine RecoveryRawLiteralBound.machine (fun _ scanned=>scanned 28)
def Inv (width : Nat) (x : State) := x.Valid ∧ x.stream.width=width
def bodyBudget (width : Nat) := 2097152*(width+1)^2
def budget (width total : Nat) := total*(bodyBudget width+3)+3

theorem budget_bound (width total : Nat) (h : total ≤ 3*(width+1)) :
    budget width total ≤ 8388608*(width+1)^3 := by
  unfold budget bodyBudget
  calc
    _ ≤ 3*(width+1)*(2097152*(width+1)^2+3)+3 := by gcongr
    _ ≤ _ := by nlinarith [show 0<(width+1)^3 by positivity]

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralLoop
