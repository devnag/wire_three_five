import Proof.MachineModel.Runs
import Proof.PCP.VerifierDecodingCompare

/-! One actual scan splits the retained child counter at the original
window counter, producing both capped count and nonnegative offset. -/
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DeltaSplitCounters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open RecoveryExecution NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨1,![none,none,some false,some false],fun _=>.right⟩
    else if q=1 then some (if bits 0 then
      ⟨1,![none,none,if bits 1 then some true else none,if bits 1 then none else some true],
        ![.right,.right,if bits 1 then .right else .stay,if bits 1 then .stay else .right]⟩
      else ⟨2,fun _=>none,fun _=>.stay⟩) else none

theorem write_word (n : Nat) :
    writeTapeBit (false::List.replicate n true) (n+1) true=false::List.replicate (n+1) true := by
  simpa only [List.length_cons,List.length_replicate,List.cons_append,List.replicate_add,List.replicate_one]
    using Streaming.write_append (false::List.replicate n true) true

noncomputable def returned := MaskedReset.machine machine (fun _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.DeltaSplitCounters
