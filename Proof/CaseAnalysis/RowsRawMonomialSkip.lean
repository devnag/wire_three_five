import Proof.CaseAnalysis.RowsRawProductRow

/-! After a product row the left stream advances once. This is the
source-only projection of the checked monomial copier, with the identical
finite control and instruction count and no discarded output buffer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawMonomialSkip
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨if bits 0 then 1 else 2,fun _=>none,fun _=>.right⟩
    else if q=1 then some ⟨if bits 0 then 1 else 0,fun _=>none,fun _=>.right⟩ else none

end NearCubicWires.RepairOrdinary.CloseoutRowsRawMonomialSkip
