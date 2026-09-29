import Proof.CaseAnalysis.RowsModeHashGuard

/-! The same computed hash-cell flags select the literal and accumulate the
unmasked child cardinality required by structuralDeltaFactor's offset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralSelect
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine (mode : Fin 3) : Machine 7 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q bits=>if q=0 then some ⟨1,
    fun i=>if i=4 then some (bits (mode.castAdd 4)&&bits 3)
      else if i=5 then some (if mode=2 then bits (mode.castAdd 4) else false)
      else if i=6 ∧ bits 2 then some true else none,
    fun i=>if i=6 ∧ bits 2 then .right else .stay⟩ else none

end NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralSelect
