import Proof.CaseAnalysis.RowsModeHashSource
import Proof.CaseAnalysis.RowsRawAtomRound

/-! Physical conditional monomial delimiters share the existing original
index copier. A retained bit closes exactly the monomial that was opened. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralMarks
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


def mark (first : Bool) : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q bits=>if q=0 then
    let flag:=if first then bits 0 else bits 4
    some ⟨1,fun i=>if i=4 ∧ first then some (bits 0) else if i=2 ∧ flag then some first else none,
      fun i=>if i=2 ∧ flag then .right else .stay⟩ else none

noncomputable def emit (b : Bool):=TapeEmbedding.machine 1 (CloseoutRowsRawAtomRound.mark b)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralMarks
