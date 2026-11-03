import Proof.SourceAssembly.SourceBundle
import Proof.PCP.VerifierDecodingCompare
import Proof.CaseAnalysis.FinalCacheRewind

/-! One actual scan splits the retained child counter at the original
window counter, producing both capped count and nonnegative offset. -/
namespace NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨1,fun _=>none,![.right,.right,.stay,.stay]⟩
    else if q=1 then some (if bits 0 then
      ⟨1,![none,none,if bits 1 then some true else none,if bits 1 then none else some true],
        ![.right,.right,if bits 1 then .right else .stay,if bits 1 then .stay else .right]⟩
      else ⟨2,fun _=>none,fun _=>.stay⟩) else none

end NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin

/-! Complete executed counter split, including zero, with its own entry
head advance and a paid return for reuse of the original counters. -/
namespace NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin

namespace NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding
/-- Same existing split execution, with a paid cold recording log. -/
def split := CloseoutFinalC10ColdCacheRewind.machine PCJ6e421fabe2aa4155_SourceLiveMin.machine

end NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin
