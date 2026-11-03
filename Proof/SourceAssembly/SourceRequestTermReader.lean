import Proof.SourceAssembly.SourceRequestMonomialSpec
import Proof.CaseAnalysis.RowsEstimatorCoefficientsProductRead
import Proof.CaseAnalysis.WitnessBoundedFields

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermReader
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.CanonicalBinary NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients

/-- One raw term code → `(coefficient, circuit code)`. -/
def termOf (t : Nat) : Option (ℚ × Nat) :=
  match decodeTaggedList t with
  | some [a, b] => (decodeCanonicalRational a).map fun coef => (coef, b)
  | _ => none

/-- One guessed sum's raw term list from its code: `(coefficient, circuit code)` per term, in the sum's order. -/
def rawSum (code : Nat) : Option (List (ℚ × Nat)) :=
  match decodeTaggedList code with
  | some [_, termsCode] => (decodeBalancedList termsCode).bind fun ts => ts.mapM termOf
  | _ => none

/-- **The `j`-th proof variable's raw term list**, read off the witness's family field. -/
noncomputable def rawTerms (bits : List Bool) (j : Nat) : Option (List (ℚ × Nat)) :=
  (decodeBalancedList (RadixSemantics.value (RepairOrdinary.CloseoutWitness.BoundedFields.family bits))).bind
    fun cs => cs[j]?.bind rawSum

end NearCubicWires.SourceRequest.TermReader
