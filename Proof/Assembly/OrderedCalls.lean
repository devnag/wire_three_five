import Proof.CaseAnalysis.FinalGuardedStageConsumer
import Proof.CaseAnalysis.FinalRetainedPhaseFold
import Proof.CaseAnalysis.RowsOriginalClauseLoop
import Proof.CaseAnalysis.FinalExactFraction

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ2f4bbfb841674a7c_
open NearCubicWires ComponentwisePolynomial RepairOrdinary
open CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open CloseoutFinalC10WorkerChain CloseoutFinalC10Exactness CloseoutFinalC10SupplierCalls

/-- Semantic matching may reorder monomials; the physical record stream is unchanged. -/
def OrderedCalls {Atom : Type} (supplier : List Atom → Rat)
 (monomials : List (CircuitMonomial Atom 4)) (entries : List Entry) : Prop :=
 ∃ order, monomials.Perm order ∧ List.Forall₂ (Calls supplier) order entries

theorem folded_value_of_orderedCalls {Atom : Type} (supplier : List Atom → Rat)
 (width : Nat) (polynomial : CircuitPolynomial Atom 4) (entries : List Entry)
 (hcalls : OrderedCalls supplier polynomial.monomials entries)
 (hvalid : ∀ estimate ∈ contributions entries, CompetitorValidity.Estimate.Valid estimate width) :
 (((CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)).value : Rat) : Real)=
 polynomial.estimatedMean supplier := by
 obtain ⟨order,hperm,hcalls⟩ := hcalls
 let ordered : CircuitPolynomial Atom 4 := ⟨order⟩
 have h := folded_value_eq_estimatedMean supplier width ordered entries hcalls hvalid
 refine h.trans ?_
 exact (hperm.map (fun m => (m.coefficient : Real)*(supplier m.factors : Real))).sum_eq.symm

end PCJ2f4bbfb841674a7c_
