import Proof.Supplier.SupplierEstimator

/-! A.12's occurrence-preserving expansion in a concrete list order. Repeated
monomials remain repeated list entries. This is the semantic output of the
remaining physical subset enumerator, not a machine realization assumption. -/
namespace NearCubicWires.RepairOrdinary.RowBinLift
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- Ascending subset size, then the standard `sublistsLen` order. The signed
coefficient is a scalar; its magnitude never creates additional occurrences. -/
def terms {α : Type} (Q : ℕ) (monomials : List (List α)) : List (ℤ × List α) :=
  (List.range (min Q monomials.length)).flatMap fun j =>
    (monomials.sublistsLen (j+1)).map fun selected => ((-2 : ℤ)^j,selected.flatten)

theorem sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum=∑ j ∈ Finset.range n,f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ,Finset.sum_range_succ,ih]

theorem terms_length {α : Type} (Q : ℕ) (monomials : List (List α)) :
    (terms Q monomials).length=
      ∑ j ∈ Finset.range (min Q monomials.length),monomials.length.choose (j+1) := by
  simp [terms,List.length_flatMap,sum_range]

end NearCubicWires.RepairOrdinary.RowBinLift
