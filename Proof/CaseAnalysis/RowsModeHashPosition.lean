import Proof.CaseAnalysis.RowsModeHashReturned

/-! Position the original lower-diagonal and translation cursors for the
next hash row by scanning the incremented original row template. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashPosition
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨1,fun _=>none,![.right,.stay,.right]⟩
    else if q=1 then some (if bits 0 then ⟨1,fun _=>none,![.right,.right,.stay]⟩
      else ⟨2,fun _=>none,![.left,.stay,.stay]⟩) else none


end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashPosition
