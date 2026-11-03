import Proof.CaseAnalysis.RowsRawPairReusable

/-! Erase a raw polynomial by its actual delimiters. Padding is not scanned. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionErase
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def next (q : Fin 4) (bit : Bool) : Fin 4 :=
  if q=0 then if bit then 1 else 3 else if q=1 then if bit then 2 else 0 else if bit then 2 else 1
def machine : Machine 1 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=3)
  rule:=fun q bits=>if q=3 then none else some ⟨next q (bits 0),fun _=>some false,fun _=>.right⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionErase
