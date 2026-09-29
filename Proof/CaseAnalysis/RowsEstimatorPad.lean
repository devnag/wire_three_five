import Proof.CaseAnalysis.RowsEstimatorWhole

/-! Paid allocation after the mandatory cold prefix. Each existing bit is
read and written unchanged; the same pass supplies all missing zero cells.
The unary D driver is retained and the ordinary rewind produces its log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Pad
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw (t : ℕ) : Machine (t+1) 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bs=>if q.val=0 then
    if bs ((0 : Fin 1).natAdd t) then
      some ⟨0,Fin.addCases (fun i=>some (bs (i.castAdd 1))) (fun _=>none),fun _=>.right⟩
    else some ⟨1,fun _=>none,fun _=>.stay⟩
    else none

def machine (t : ℕ) := Rewind.machine (raw t)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Pad
