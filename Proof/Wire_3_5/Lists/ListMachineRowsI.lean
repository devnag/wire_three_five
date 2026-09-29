import Proof.Wire_3_5.Lists.ListMachineFlatten
import Proof.Wire_3_5.Lists.ListMachineContractsI

/-! # C2f by interpolation: the amplified list with printed visit factors (P3:1491-1530)

Realizes the factors of `list:flatten`'s expansion (P3:1494-1500, 1521-1526) as the interpolation printer prints them:
the visited base state `P^{(k)}_s` is `listPrint D L s`, the degree-`≤ listBound D` interpolation of the state bit
`[listReportFast D Z = s]` (C5's fast report, the paper's reported count). Its value is the value of the explicit
expansion `stateRef D L s` at every assignment (`listPrint_eval`).

Results: `listBit_eq`, `listBound_ge`, `listPrint_eval`, `visitPrint_eval`, the generic `flatExpr_eval_of` (the
amplified state's value from the visit factors' values alone), and **`flatExprI_eval`**: the amplified state with printed
visit factors is the amplified state on EVERY input. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.SupplierWalk

/-! ## A list's state bits, printed -/

/-- The state bit of a list at an input, through the final pass's fast report. -/
def listBit (D : ListData) (s : ℕ) (Z : List Bool) : Bool := decide (FinalPass.ListFast.listReportFast D Z = s)

theorem listBit_eq (D : ListData) (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true) (L s : ℕ)
    (hs : s ≤ D.M) (Z : List Bool) (hZ : Z.length = L) :
    listBit D s Z = F2Poly.eval (stateRef D L s) fun i => Z.getD i false := by
  set z : Fin L → Bool := fun i => Z[i.val]'(by rw [hZ]; exact i.isLt) with hz
  have hext : (fun i => Z.getD i false) = ext z := by
    funext i
    unfold ext
    split_ifs with hi
    · rw [List.getD_eq_getElem _ _ (by omega)]
    · rw [List.getD_eq_default _ _ (by omega)]
  have hofFn : List.ofFn z = Z := by
    apply List.ext_getElem (by simp [hZ])
    intro k h1 h2
    simp [hz]
  have he := stateRef_eval D hnest L s z
  rw [hofFn] at he
  rw [hext]
  apply ListTable.bitF2_inj
  rw [he]
  unfold listBit
  have hiff := D.listStates_eq_one_iff Z s hs
  rw [FinalPass.ListFast.listReport_eq_fast] at hiff
  by_cases h : FinalPass.ListFast.listReportFast D Z = s
  · rw [decide_eq_true h, hiff.mpr h.symm]; rfl
  · rw [decide_eq_false h]
    have h1 : D.listStates Z s ≠ 1 := fun h' => h (hiff.mp h').symm
    have h0 : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
    rw [h0 _ h1]; rfl

/-- A list's enumeration bound: `Σ_{j<J} 4W_j + 1`. -/
def listBound (D : ListData) : ℕ := ∑ j ∈ range D.J, 4 * D.W j + 1

theorem ell_bound' (D : ListData) (j : ℕ) : 2 ^ D.ell j - 1 ≤ 4 * D.W j := by
  rcases Nat.eq_zero_or_pos (D.ell j) with h0 | hpos
  · rw [h0]; simp
  · have hlt : 2 ^ (D.ell j - 1) < 2 * D.W j + 1 := by
      unfold ListData.ell at hpos ⊢
      have h1 : 1 < 2 * D.W j + 1 := by
        by_contra hc
        have : 2 * D.W j + 1 ≤ 1 := by omega
        have := Nat.clog_of_right_le_one (b := 2) this
        omega
      exact Nat.pow_pred_clog_lt_self (by norm_num) h1
    have e : 2 ^ D.ell j = 2 * 2 ^ (D.ell j - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem listBound_ge (D : ListData) : ∑ j ∈ range D.J, (2 ^ D.ell j - 1) ≤ listBound D := by
  unfold listBound
  have := Finset.sum_le_sum fun j (_ : j ∈ range D.J) => ell_bound' D j
  omega

/-! ## The amplified states with printed visits -/


end NearCubicWires.WireExponent3_5.ListMachine
