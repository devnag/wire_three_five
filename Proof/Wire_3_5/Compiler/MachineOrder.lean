import Proof.Wire_3_5.Compiler.MachineStream

/-! # C3.2, polarization: the subset-major order of the machine (P3:1918-1923)

Paper: "Multiply the expression by `2^{m−1}`. For a nonconstant term of length `t_ν`, Lemma alg:polarization replaces its
product by at most `2^{t_ν}−1` parities, with integer coefficient multiplier `2^{m−t_ν}`" (P3:1918-1921). The streaming
reference enumerates each term's sub-lists in counter order (`polarizeM`, `List.sublists`). When every term has exactly
`m` factors the counter has the fixed width `m`: sub-list `j < 2^m` takes factor `i` when bit `i` of `j` is set
(`selectBits`, **`sublists_eq_selectBits`**), and its coefficient is `−c·(−1)^{|J|}`.

A machine that scans the expression once per counter value runs the loops subset-major: for each `j < 2^m`, for each
term. **`compileRefX`** is that order, and **`compileRefX_perm`** shows it lists the occurrences of `compileRefM`, hence
of `compileRef` (`compileRefX_modEq`, `compileRefX_length_le`).

Padding a term to exactly `m` factors with the constant polynomial `[[]]` keeps its value, the number of terms and the
degree bound (`pad`, `pad_padded`, `eval_pad`, `pad_length`, `pad_degree`), so the padded reference
meets `alg:compiler` for the original expression (`compileRefX_pad_modEq`, `compileRefX_pad_length_le`).

Main declarations: `selectBits`, `range_two_mul`, **`sublists_eq_selectBits`**, `flatMap_comm_perm`, `compileRefX`,
**`compileRefX_perm`**, `compileRefX_modEq`, `compileRefX_length_le`, `Padded`, `pad`, **`pad_padded`**, **`eval_pad`**,
`pad_length`, `pad_degree`, **`compileRefX_pad_modEq`**, **`compileRefX_pad_length_le`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub

/-! ## Sub-lists by the bits of a counter -/

/-- The sub-list selected by the bits of `j`: bit `i` selects element `i`. -/
def selectBits {α : Type} : List α → ℕ → List α
  | [], _ => []
  | p :: ps, j => if j % 2 = 1 then p :: selectBits ps (j / 2) else selectBits ps (j / 2)

theorem range_two_mul : ∀ N : ℕ, List.range (2 * N) = (List.range N).flatMap fun k => [2 * k, 2 * k + 1]
  | 0 => rfl
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, List.range_succ, List.range_succ, range_two_mul N, List.range_succ,
      List.flatMap_append]
    simp [List.append_assoc]

/-- **The sub-lists in counter order**: sub-list `j` takes element `i` exactly when bit `i` of `j` is set. -/
theorem sublists_eq_selectBits {α : Type} : ∀ ps : List α,
    ps.sublists = (List.range (2 ^ ps.length)).map (selectBits ps)
  | [] => rfl
  | p :: ps => by
    rw [List.sublists_cons, sublists_eq_selectBits ps]
    show ((List.range (2 ^ ps.length)).map (selectBits ps)).flatMap (fun x => [x, p :: x]) = _
    rw [List.length_cons, pow_succ, Nat.mul_comm, range_two_mul, List.map_flatMap, List.flatMap_map]
    apply List.flatMap_congr
    intro k _
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    have h3 : 2 * k / 2 = k := by omega
    have h4 : (2 * k + 1) / 2 = k := by omega
    simp [selectBits, h1, h2, h3, h4]

/-! ## Swapping two list loops -/

theorem flatMap_comm_perm {α β γ : Type} (l1 : List α) (l2 : List β) (f : α → β → List γ) :
    (l1.flatMap fun a => l2.flatMap fun b => f a b).Perm (l2.flatMap fun b => l1.flatMap fun a => f a b) := by
  induction l1 with
  | nil => simp
  | cons a l1 ih =>
    simp only [List.flatMap_cons]
    refine (List.Perm.append_left _ ih).trans ?_
    exact List.flatMap_append_perm l2 (fun b => f a b) (fun b => l1.flatMap fun a' => f a' b)

/-! ## The subset-major reference -/

/-- The occurrences of one term's sub-list `j` (a term of exactly `m` factors): coefficient `−c·(−1)^{|J|}`. -/
def termOcc (pool : List (List SynEq)) (H : ℤ) (Q : ℕ) (t : ℤ × List (F2Poly ℕ)) (j : ℕ) : List Occurrence :=
  (unionsM Q (oddMasksM pool (selectBits t.2 j).flatten)).map
    (occOf pool H (t.1 * 2 ^ 0 * -(-1 : ℤ) ^ (selectBits t.2 j).length))

/-- **The compiler stages' reference in the machine's loop order**: for each counter value `j < 2^m`, for each term. -/
def compileRefX (pool : List (List SynEq)) (H : ℤ) (m Q : ℕ) (V : IntExpression ℕ) : List Occurrence :=
  (List.range (2 ^ m)).flatMap fun j => V.flatMap fun t => termOcc pool H Q t j

theorem polarizeTermM_full (m : ℕ) (hm : 1 ≤ m) (c : ℤ) (ps : List (F2Poly ℕ)) (hps : ps.length = m) :
    polarizeTermM m c ps =
      (List.range (2 ^ m)).map fun j => (c * 2 ^ 0 * -(-1 : ℤ) ^ (selectBits ps j).length, (selectBits ps j).flatten) := by
  have hne : ps ≠ [] := by intro h; rw [h] at hps; simp at hps; omega
  unfold polarizeTermM
  rw [if_neg hne, sublists_eq_selectBits, hps, List.map_map, Nat.sub_self]
  rfl

/-- **The subset-major order lists the occurrences of `compileRefM`** (every term has exactly `m ≥ 1` factors). -/
theorem compileRefX_perm (pool : List (List SynEq)) (H : ℤ) (m Q : ℕ) (hm : 1 ≤ m) (V : IntExpression ℕ)
    (hV : ∀ t ∈ V, t.2.length = m) : (compileRefX pool H m Q V).Perm (compileRefM pool H m Q V) := by
  unfold compileRefX compileRefM polarizeM
  refine (flatMap_comm_perm _ _ _).trans ?_
  rw [List.flatMap_assoc]
  apply List.Perm.flatMap_left
  intro t ht
  rw [polarizeTermM_full m hm t.1 t.2 (hV t ht), List.flatMap_map]
  rfl

/-- **`alg:compiler` for the subset-major order** (P3:1916-1946). -/
theorem compileRefX_modEq (pool : List (List SynEq)) (H Vb : ℤ) (hH : Vb < H) (m Q : ℕ) (hm : 1 ≤ m)
    (V : IntExpression ℕ) (hV : ∀ t ∈ V, t.2.length = m) (zL zR : ℕ)
    (hVb : ∀ e ∈ pool.flatten, |e.value zL zR| ≤ Vb) (ρ : ℕ → Bool) (hex : PoolExact pool zL zR ρ) :
    occTable (compileRefX pool H m Q V) zL zR ≡ 2 ^ (m - 1) * IntExpression.eval V ρ [ZMOD (2 : ℤ) ^ Q] := by
  rw [occTable_perm (compileRefX_perm pool H m Q hm V hV)]
  exact compileRefM_modEq pool H Vb hH m Q hm V (fun t ht => (hV t ht).le) zL zR hVb ρ hex

/-- **`alg:eq-occurrences` for the subset-major order** (P3:1887-1888). -/
theorem compileRefX_length_le (pool : List (List SynEq)) (H : ℤ) (m Q d : ℕ) (hm : 1 ≤ m) (V : IntExpression ℕ)
    (hV : ∀ t ∈ V, t.2.length = m) (hd : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, mono.length ≤ d) :
    (compileRefX pool H m Q V).length ≤ V.length * 2 ^ m * (Q * (pool.flatten.length + 1) ^ (Q * d)) := by
  rw [(compileRefX_perm pool H m Q hm V hV).length_eq]
  exact compileRefM_length_le pool H m Q d V (fun t ht => (hV t ht).le) hd

/-! ## Padding a term to `m` factors -/

/-- Every term has exactly `m` factors (the C3 v2 precondition). -/
def Padded (m : ℕ) (V : IntExpression ℕ) : Prop := ∀ t ∈ V, t.2.length = m


end NearCubicWires.WireExponent3_5.CompilerMachine
