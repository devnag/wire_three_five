import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Proof.CaseAnalysis.RowsTouchingPascalNext
import Proof.CaseAnalysis.WitnessHeaderSwitch
import Proof.MachineModel.FrameSkip
import Proof.MachineModel.Layout

/-! A.4 cold start, part 4: the missing one-cell writer.

The corpus has `LookupReadBit.clear`, which writes `false` at the head, but
no mirror that writes `true`, and therefore no producer for the bare
(unframed) one-hot word that port 2 of the selector's entry bank needs.
`setOne` is that mirror: the same one-tape, two-state machine with `some
false` replaced by `some true`.  Applied to the all-blank word that
`RecoveryScratchErase`/`CloseoutRowsEstimator.Pad` already produce, one
paid step turns it into `binary q 1`, i.e. exactly `port02`. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalSelector
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- One paid step: write `true` at the head. The mirror of `LookupReadBit.clear`. -/
def setOne : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>some true,fun _=>.stay⟩ else none

theorem set_ready (bit : Bool):ReadyRun setOne 1 (fun _=>[bit]) (fun _=>[true]):=by
  let input : Configuration 1 2:=⟨0,fun _=>0,fun _=>[bit]⟩
  let output : Configuration 1 2:=⟨1,fun _=>0,fun _=>[true]⟩
  have hs:step setOne input=some output:=by rfl
  obtain ⟨r,hr,hrf,hrs⟩:=(Timed.single (by rfl : setOne.halted input.control=false) hs).run (by rfl)
  exact ⟨r,hr,by rw [hrf],by intro i;rw [hrf],hrs⟩


/-! ### The other bare cells the port chart needs

`LookupReadBit.clear` is already accepted; these are the two instances the
selector's entry bank asks for and that nothing had stated before. -/

end NearCubicWires.RepairOrdinary.CloseoutFinalSelector
