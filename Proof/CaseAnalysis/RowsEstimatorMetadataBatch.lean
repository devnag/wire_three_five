import Proof.CaseAnalysis.RowsEstimatorPad
import Proof.CaseAnalysis.RowsMetadataCopy

/-! All caller metadata fields are copied in parallel in one paid D pass.
The source bank, raw D, and the reusable rewind log are preserved. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.MetadataBatch
open LocalBitMultitape RecoveryRootRound RecoveryExecution RecoveryBoundedTapeCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw (k : ℕ) : Machine (k+(k+1)) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bs => if q.val=0 then
    if bs (((0 : Fin 1).natAdd k).natAdd k) then
      some ⟨0,Fin.addCases (fun _ : Fin k => none)
        (Fin.addCases (fun i : Fin k => some (bs (i.castAdd (k+1)))) (fun _ : Fin 1 => none)),
        fun _ => .right⟩
    else some ⟨1,fun _ => none,fun _ => .stay⟩
    else none

def machine (k : ℕ) := Rewind.machine (raw k)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.MetadataBatch
