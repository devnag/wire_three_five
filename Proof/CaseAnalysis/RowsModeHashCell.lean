import Proof.CaseAnalysis.RowsModeHashLoop

/-! The actual hash-prefix scan returns all three literal cell flags:
zero prefix, its one-bit sibling, and its zero child. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashCell
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 5 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨1,fun i=>if i=2 then some true else none,fun _=>.stay⟩
    else if q=1 then some (if bits 1 then ⟨1,fun i=>if i=2 then some (bits 2&&!bits 0) else none,
      ![.right,.right,.stay,.stay,.stay]⟩ else ⟨2,![none,none,none,some (bits 2&&bits 0),some (bits 2&&!bits 0)],fun _=>.stay⟩)
    else none


end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashCell
