import Proof.Amplification.RecoveryBoundedWordCopy

/-! Exact all-word semantics of the bounded witness copy, including short
witnesses: the retained table source is the framed truncated prefix, padded
with physically allocated false cells. No witness-length premise is used. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedWordCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryBoundedTapeCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copied_nil (count : Nat) : copied [] count=List.replicate count false := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [prefix_succ,ih]
    simp [readTapeBit,List.getD,List.replicate_add]

theorem copied_cons (bit : Bool) (source : List Bool) (count : Nat) :
    copied (bit::source) (count+1)=bit::copied source count := by
  simp [copied,List.range_succ_eq_map,List.map_map,Function.comp_def,readTapeBit,List.getD]

theorem closed_frame (word : List Bool) (cap : Nat) :
    copied (frame word) (2*cap)++[false]=ZeroPadding.pad (2*cap+1) (frame (word.take cap)) := by
  induction cap generalizing word with
  | zero => simp [copied,ZeroPadding.pad,frame]
  | succ cap ih =>
    cases word with
    | nil =>
      simp [frame,Nat.mul_add,copied_cons,copied_nil,ZeroPadding.pad,List.replicate_succ]
      rw [← List.replicate_succ',List.replicate_succ]
    | cons bit rest =>
      have h := ih rest
      simpa [frame,Nat.mul_add,copied_cons,ZeroPadding.pad_cons,Nat.add_assoc] using
        congrArg (fun tail=>true::bit::tail) h

end NearCubicWires.RepairOrdinary.RecoveryBoundedWordCopy
