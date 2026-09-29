import Proof.Supplier.RowBinLiftCuts

/-! The shared A.12 row consumer, with width derived from emitted data and
gate capacity discharged by the paper's actual residual gate hypothesis. -/
namespace NearCubicWires.RepairOrdinary.RowBinLift
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open MatrixScoreBatch EquationRow ExecutableInterfaces
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def batch {l r : ℕ} (Q : ℕ) (rows : List (List (List (Equation l r)))) : List Cut :=
  rows.flatMap (cuts Q)

theorem terms_length_bound {α : Type} (Q : ℕ) (monomials : List (List α)) :
    (terms Q monomials).length ≤ Q*max 1 monomials.length^Q := by
  rw [terms_length]
  calc
    _ ≤ ∑ _j ∈ Finset.range (min Q monomials.length),max 1 monomials.length^Q := by
      apply Finset.sum_le_sum
      intro j hj
      have hjQ : j+1 ≤ Q := (Finset.mem_range.mp hj) |>.trans_le (Nat.min_le_left _ _)
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (Nat.le_max_right _ _) _).trans
          (Nat.pow_le_pow_right (Nat.le_max_left _ _) hjQ))
    _ = min Q monomials.length*(max 1 monomials.length^Q) := by simp
    _ ≤ Q*max 1 monomials.length^Q := Nat.mul_le_mul_right _ (Nat.min_le_left _ _)

theorem batch_length_bound {l r : ℕ} (Q N : ℕ)
    (rows : List (List (List (Equation l r))))
    (hN : ∀ ms ∈ rows,ms.length ≤ N) :
    (batch Q rows).length ≤ rows.length*Q*max 1 N^Q := by
  have hs : ((rows.map (fun ms => (cuts Q ms).length))).sum ≤
      rows.length*(Q*max 1 N^Q) := by
    induction rows with
    | nil => simp
    | cons ms rows ih =>
      have hm := terms_length_bound Q ms
      have hp : max 1 ms.length ≤ max 1 N := max_le_max (by rfl) (hN ms (by simp))
      have hb : (cuts Q ms).length ≤ Q*max 1 N^Q := by
        simpa only [cuts,List.length_map] using
          hm.trans (Nat.mul_le_mul_left Q (Nat.pow_le_pow_left hp Q))
      have ht := ih (fun a ha => hN a (by simp [ha]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  simpa only [batch,List.length_flatMap,Nat.mul_assoc] using hs

def fieldMass (cs : List Cut) : ℕ :=
  ((cs.flatMap fields).map Int.natAbs).sum

def fieldWidth (cs : List Cut) : ℕ := Nat.log 2 (fieldMass cs)+1

theorem member_le_sum (ns : List ℕ) (n : ℕ) (hn : n ∈ ns) : n ≤ ns.sum := by
  induction ns with
  | nil => simp at hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with rfl | ht
    · simp
    · exact (ih ht).trans (Nat.le_add_left _ _)

theorem field_fit (cs : List Cut) (c : Cut) (hc : c ∈ cs)
    (z : ℤ) (hz : z ∈ fields c) : z.natAbs < 2^fieldWidth cs := by
  have hm : z.natAbs ≤ fieldMass cs := member_le_sum _ _
    (List.mem_map.mpr ⟨z,List.mem_flatMap.mpr ⟨c,hc,hz⟩,rfl⟩)
  exact hm.trans_lt (Nat.lt_pow_succ_log_self (by decide) _)

theorem fields_fit (cs : List Cut) (c : Cut) (hc : c ∈ cs) : Fits (fieldWidth cs) c := by
  refine ⟨?_,?_,?_⟩
  · intro w hw
    exact field_fit cs c hc w (List.mem_append_left _ hw)
  · exact field_fit cs c hc c.threshold (by simp [fields])
  · exact field_fit cs c hc c.coefficient (by simp [fields])

end NearCubicWires.RepairOrdinary.RowBinLift
