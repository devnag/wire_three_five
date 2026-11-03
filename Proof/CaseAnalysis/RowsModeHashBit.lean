import Mathlib.Data.Nat.Choose.Lucas
import Proof.CaseAnalysis.RowsDegreeAdvance
import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.CaseAnalysis.RowsModeElementary
import Proof.CaseAnalysis.RowsModeWindowBinomial
import Proof.CaseAnalysis.RowsModeWindowScalar
import Proof.Circuits.ValidatorPolynomialDomination
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.MachineModel.OrdinaryFramedIncrement
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.MachineModel.OrdinaryZeroUnpadding
import Proof.Supplier.RowTupleTerms

/-! One Toeplitz output bit scans the original lower diagonals backwards
and upper diagonals forwards. No row matrix or reversed seed is supplied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashBit
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 7 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=3)
  rule:=fun q bits=>
    if q=0 then some ⟨1,fun i=>if i=6 then some (bits 5) else none,fun _=>.stay⟩
    else if q=1 then some ⟨if bits 4 then 1 else 2,
      fun i=>if i=6 then some (xor (bits 6) (bits 1&&bits 2)) else none,
      ![.right,.right,.left,.stay,.left,.stay,.stay]⟩
    else if q=2 then some (if bits 0 then ⟨2,
      fun i=>if i=6 then some (xor (bits 6) (bits 1&&bits 3)) else none,
      ![.right,.right,.stay,.right,.stay,.stay,.stay]⟩
      else ⟨3,fun _=>none,fun _=>.stay⟩)
    else none


end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashBit
