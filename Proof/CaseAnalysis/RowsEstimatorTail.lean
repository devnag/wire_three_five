import Proof.CaseAnalysis.RowsEstimatorScan

/-! Append the actual parity bit and exact cut bytes after the paid header.
The length driver is the scanner's output, never an assumed count stream. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Tail
open LocalBitMultitape RecoveryExecution Streaming RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bs=>if q.val=0 then
      some ⟨1,![none,none,none,some (bs 2)],![.stay,.stay,.stay,.right]⟩
    else if q.val=1 then
      if bs 1 then some ⟨1,![none,none,none,some (bs 0)],![.right,.right,.stay,.right]⟩
      else some ⟨2,fun _=>none,fun _=>.stay⟩
    else none

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Tail
