import Proof.CaseAnalysis.RowsEstimatorInput

/-! Paid counting of the original cut stream. A retained field-count template
separates cuts; the scanner reads every frame marker and payload transition.
The second output is the literal byte length needed by the outer framer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scan
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 7 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==6
  rule:=fun q bs=>if q.val=0 then
      some ⟨1,fun _=>none,![.stay,.right,.stay,.stay]⟩
    else if q.val=1 then
      if bs 0 then some ⟨2,![none,none,some true,none],![.stay,.stay,.right,.stay]⟩
      else some ⟨6,fun _=>none,fun _=>.stay⟩
    else if q.val=2 then
      if bs 1 then some ⟨3,fun _=>none,![.stay,.right,.stay,.stay]⟩
      else some ⟨5,fun _=>none,![.stay,.left,.stay,.stay]⟩
    else if q.val=3 then
      some ⟨if bs 0 then 4 else 2,![none,none,none,some true],![.right,.stay,.stay,.right]⟩
    else if q.val=4 then
      some ⟨3,![none,none,none,some true],![.right,.stay,.stay,.right]⟩
    else if q.val=5 then
      some ⟨if bs 1 then 5 else 1,fun _=>none,![.stay,if bs 1 then .left else .right,.stay,.stay]⟩
    else none

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scan
