import Proof.CaseAnalysis.RowsSupportTyped
import Proof.CaseAnalysis.RowsTupleSeekPairs
import Proof.MachineModel.CacheRewind
import Proof.MachineModel.Encoding

/-! The paper's native identity-bottom parity circuit, in increasing support order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open Finset SupplierPipeline SourceInterfaces
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem foldl_xor_eq_decide_odd_countP {Alpha : Type}
    (select : Alpha → Bool) (elements : List Alpha) (accumulator : Bool) :
    elements.foldl
        (fun parity element => xor parity (select element)) accumulator =
      xor accumulator (decide (Odd (elements.countP select))) := by
  induction elements generalizing accumulator with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis, List.countP_cons]
      by_cases hhead : select head = true
      · rcases Nat.mod_two_eq_zero_or_one (tail.countP select) with
          hparity | hparity
        · cases accumulator <;>
            simp [hhead, Nat.odd_add_one, Nat.odd_iff, hparity]
        · cases accumulator <;>
            simp [hhead, Nat.odd_add_one, Nat.odd_iff, hparity]
      · simp only [Bool.not_eq_true] at hhead
        simp [hhead]

theorem parityOn_eq_decide_odd_filter_card {n : ℕ}
    (support : Finset (Fin n)) (input : BitInput n) :
    parityOn support input =
      decide (Odd ((support.filter fun coordinate => input coordinate).card)) := by
  rw [parityOn, foldl_xor_eq_decide_odd_countP]
  simp only [Bool.false_xor]
  congr 2
  calc
    support.toList.countP input =
        support.toList.countP
          (fun coordinate => decide (input coordinate = true)) := by
      congr 2
      funext coordinate
      cases input coordinate <;> rfl
    _ = Multiset.countP (fun coordinate => input coordinate = true)
        support.val := by
      rw [← Finset.coe_toList]
      rfl
    _ = (support.filter fun coordinate => input coordinate).card := by
      rw [Multiset.countP_eq_card_filter]
      rfl


end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
