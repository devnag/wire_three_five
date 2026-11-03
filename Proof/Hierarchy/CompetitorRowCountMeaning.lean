import Proof.Hierarchy.CompetitorCrossStateMeaning
import Proof.Supplier.RowPowerBinLift

/-! The actual weighted bank sum is congruent to the list of Boolean row
values. Repeated rows and monomial occurrences retain their multiplicity.
The width of the executed request is independent of the semantic radix. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRowCountMeaning
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope MatrixScoreBatch EquationRow RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def occurrence {l r : ℕ} (ms : List (List (Equation l r))) (row column : ℕ) : ℕ :=
  polynomialOccurrenceCount
    (fun e (_ : Unit) (_ : Unit) => decide (e.Holds (assignment row column))) ms () ()

def count {l r : ℕ} (rows : List (List (List (Equation l r)))) (row column : ℕ) : ℕ :=
  (rows.map (fun ms => occurrence ms row column%2)).sum

theorem odd_even_size (input : EquationRow.Input) (ho : input.odd=true) :
    (request input).U/2+(request input).U/2=(request input).U := by
  have hd := input.oddPositive ho
  have he : input.d=input.d-1+1 := by omega
  change 2^input.d/2+2^input.d/2=2^input.d
  rw [he,pow_succ]
  rw [Nat.mul_div_cancel _ (by decide : 0<2)]
  omega

end NearCubicWires.RepairOrdinary.CompetitorRowCountMeaning
