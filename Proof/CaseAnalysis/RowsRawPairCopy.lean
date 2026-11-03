import Proof.CaseAnalysis.RowsRawPairSeekBody
import Proof.CaseAnalysis.RowsRawAtomRead

/-! Residualization appends the original and frozen-gate atom bodies under
one polynomial delimiter. No X/C pattern is chosen from a column: the
physical output is their characteristic-two sum. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPairCopy
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawPolynomialAdd
open CloseoutRowsRawPairSeek (Pair word)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boundary (emit : Bool) : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,
    ![none,none,if emit then some false else none,none,none],
    ![.stay,.right,if emit then .right else .stay,.stay,.stay]⟩ else none
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine rightMachine (boundary false)) rightMachine) (boundary true)

end NearCubicWires.RepairOrdinary.CloseoutRowsRawPairCopy
