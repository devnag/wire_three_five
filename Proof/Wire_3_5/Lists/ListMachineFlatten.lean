import Proof.Wire_3_5.Lists.ListMachineNormal
import Proof.Wire_3_5.Lists.ListFlatten

/-! # C2f computable refs: the amplified list as a factored integer expression (P3:1491-1530)

Realizes the expansion half of `list:flatten` (P3:1494-1500, 1521-1526): "Each state is an exact integer polynomial with
`O_D(L)` base Boolean factors per term, `n^{O_D(1)}` terms [...] The ordinary integer multilinear expansion of
majority on `t` bits has at most `2^t` terms [...] The repaired zero coordinate equals
`1 − Σ_{s>0} Maj_t(P^{(1)}_s, …, P^{(t)}_s)` over the integers, because the majority vector is at most one-hot."

The machine prints each amplified state as S0's `IntExpression ℕ` (the input type of the compiler
`Compiler.compileExpression`), KEPT FACTORED: every term is `±1` times exactly `t` base factors, the visited base
states `P^{(k)}_s` (reduced lists, `Ref.stateRefN`) or their complements `1 − P^{(k)}_s`. It is never multiplied out,
so the base degree `O(√B + L)` is not multiplied by `t` (P3:1497-1500).

Main quantities: `allRows t` (the `2^t` truth-table rows), `rowFactors` (the `t` factors of a row), **`majTerms t θ P`**
(the truth-table expansion `Σ_{|T| ≥ θ} Π_{k∈T} P_k Π_{k∉T}(1 − P_k)`), **`flatExpr`** (the amplified state `s`: the
majority for `s ≥ 1`, and `1 − Σ_{s'=1}^M Maj_t(…)` for `s = 0`), and `flatExprOf P e L s` (with the visited base
states of `FlatListParams`). Results: `majTerms_eval` (the expansion is the majority indicator on EVERY
input), **`flatExprOf_eval`** (the printed expression is `1[flatReport = s]` on EVERY input), and
`flatExpr_size` (`≤ (M+1)·2^t` terms, at most `t` factors each). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.SupplierWalk

/-! ## Integer expressions -/

/-- A factored integer expression over the coordinates (S0's `IntExpression ℕ`). -/
abbrev Expr := IntExpression ℕ

theorem expr_eval_cons (c : ℤ) (fs : List Poly) (V : Expr) (ρ : ℕ → Bool) :
    IntExpression.eval ((c, fs) :: V) ρ = c * (fs.map fun p => bitZ (F2Poly.eval p ρ)).prod + IntExpression.eval V ρ := by
  simp [IntExpression.eval]

theorem expr_eval_append (V W : Expr) (ρ : ℕ → Bool) :
    IntExpression.eval (V ++ W) ρ = IntExpression.eval V ρ + IntExpression.eval W ρ := by
  simp [IntExpression.eval]

theorem expr_eval_flatMap {β : Type} (l : List β) (f : β → Expr) (ρ : ℕ → Bool) :
    IntExpression.eval (l.flatMap f) ρ = (l.map fun b => IntExpression.eval (f b) ρ).sum := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, expr_eval_append, ih, List.map_cons, List.sum_cons]

/-! ## The truth-table majority expansion -/

/-- All `2^t` Boolean rows of length `t`. -/
def allRows : ℕ → List (List Bool)
  | 0 => [[]]
  | t + 1 => (allRows t).flatMap fun r => [false :: r, true :: r]

/-- The factors of a row, from position `o`: `P_k` where the row is true, `1 − P_k` where it is false. -/
def rowFactors (P : ℕ → Poly) : ℕ → List Bool → List Poly
  | _, [] => []
  | o, x :: r => (if x then P o else nnot (P o)) :: rowFactors P (o + 1) r

/-- The factor product of a row at an assignment. -/
def rowProd (P : ℕ → Poly) (ρ : ℕ → Bool) (o : ℕ) (r : List Bool) : ℤ :=
  ((rowFactors P o r).map fun p => bitZ (F2Poly.eval p ρ)).prod

/-- The bits the factors take at an assignment, from position `o`. -/
def bitsFrom (P : ℕ → Poly) (ρ : ℕ → Bool) (o t : ℕ) : List Bool := (List.range t).map fun k => F2Poly.eval (P (o + k)) ρ

theorem bitsFrom_succ (P : ℕ → Poly) (ρ : ℕ → Bool) (o t : ℕ) :
    bitsFrom P ρ o (t + 1) = F2Poly.eval (P o) ρ :: bitsFrom P ρ (o + 1) t := by
  unfold bitsFrom
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero, Function.comp_def]
  congr 2
  funext k
  rw [Nat.add_assoc, Nat.add_comm 1 k]

theorem sum_flatMap_pair (l : List (List Bool)) (F : List Bool → ℤ) :
    ((l.flatMap fun r => [false :: r, true :: r]).map F).sum = (l.map fun r => F (false :: r) + F (true :: r)).sum := by
  induction l with
  | nil => rfl
  | cons r l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih]; simp [add_assoc]

/-- **Exactly one row matches**: `Σ_r g(r) Π_k [r_k = b_k] = g(b)` (the rows' indicators are disjoint). -/
theorem sum_rows_select (P : ℕ → Poly) (ρ : ℕ → Bool) (t : ℕ) :
    ∀ (o : ℕ) (g : List Bool → ℤ),
      ((allRows t).map fun r => g r * rowProd P ρ o r).sum = g (bitsFrom P ρ o t) := by
  induction t with
  | zero => intro o g; simp [allRows, rowProd, rowFactors, bitsFrom]
  | succ t ih =>
    intro o g
    set b := F2Poly.eval (P o) ρ with hb
    have hrow : ∀ r, rowProd P ρ o (false :: r) = bitZ (!b) * rowProd P ρ (o + 1) r ∧
        rowProd P ρ o (true :: r) = bitZ b * rowProd P ρ (o + 1) r := by
      intro r
      simp [rowProd, rowFactors, eval_nnot, hb]
    have hsum : ((allRows (t + 1)).map fun r => g r * rowProd P ρ o r).sum =
        ((allRows t).map fun r => (bitZ (!b) * g (false :: r) + bitZ b * g (true :: r)) * rowProd P ρ (o + 1) r).sum := by
      simp only [allRows]
      rw [sum_flatMap_pair]
      congr 1
      apply List.map_congr_left
      intro r _
      rw [(hrow r).1, (hrow r).2]
      ring
    rw [hsum, ih (o + 1) (fun r => bitZ (!b) * g (false :: r) + bitZ b * g (true :: r)), bitsFrom_succ, ← hb]
    cases b <;> simp [bitZ]

/-! ## The amplified states -/

theorem count_ofFn_true : ∀ (t : ℕ) (y : Fin t → Bool),
    (List.ofFn y).count true = (Finset.univ.filter fun k => y k = true).card
  | 0, y => by simp
  | t + 1, y => by
    rw [List.ofFn_succ, List.count_cons, count_ofFn_true t, Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_succ]
    cases y 0 <;> simp [add_comm]

/-! ## Size -/

theorem mem_allRows_length {t : ℕ} {r : List Bool} (h : r ∈ allRows t) : r.length = t := by
  induction t generalizing r with
  | zero => simp [allRows] at h; subst h; rfl
  | succ t ih =>
    simp only [allRows, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at h
    obtain ⟨r', hr', rfl | rfl⟩ := h <;> simp [ih hr']

end NearCubicWires.WireExponent3_5.ListMachine
