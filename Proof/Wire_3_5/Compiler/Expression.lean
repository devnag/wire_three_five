import Proof.Wire_3_5.Compiler.Substitute
import Proof.Wire_3_5.Compiler.StackLift

/-! # `alg:compiler` (P3:1874-1955) and `alg:recovery` (P3:1965-1982)

Realizes `alg:compiler`: "Let `V(z) = Σ_{ν=1}^A c_ν ∏_{j=1}^{t_ν} p_{ν,j}(z)`, `0 ≤ t_ν ≤ m`, be an explicit integer
expression [...] choose `Q ≥ 1` with `2^Q > J`, and put `Q' = Q+m−1`. There is an explicit signed separated-equation
expression congruent to `2^{m−1}V(z)` modulo `2^{Q'}`, with at most `𝒮 ≤ A 2^m Q'(P_ex+1)^{Q'd}` occurrences. Each
occurrence stacks at most `Q'd` original exact equations" (P3:1880-1897), by the paper's proof: polarization
(`alg:polarization`), substitution of the disjoint exact children with cancellation, `alg:binlift` at precision `Q'`,
and `alg:stack` (P3:1916-1946); and `alg:recovery`: "A signed expression congruent to an integer `W(z)` modulo `2^q`
recovers `W` column by column if either `0 ≤ W(z) < 2^q` everywhere, or `|W(z)| ≤ J` everywhere and `2^q > 2J`"
(P3:1967-1972).

Inputs: atoms `α` with child labels `children : α → List ℕ` and child equations `eqs : ℕ → SeparatedEquation ZL ZR`
(the disjoint exact children of `alg:pullback`), a stacking base `H` above the children's magnitude bound, the arity bound
`m` and the precision `Q'`.

Main declarations: `conjEquation`, `supportUnion`, `liftOccurrences`, **`compileExpression`** (the ref:
`IntExpression → SignedOccurrenceList`); **`compileExpression_modEq`** (the congruence); **`compileExpression_length_le`**
(the occurrence bound) and `mem_compileExpression_stack_le` (at most `Q'd` stacked equations); `recoverColumn`,
**`recoverColumn_eq`**, `recoverSigned`, **`recoverSigned_eq`**; **`compileExpression_recover`** (the complete column value
`2^{m−1}V(z)` is recovered exactly as the least residue when `0 ≤ V ≤ J`, `2^{m−1}J < 2^{Q'}`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

variable {α ZL ZR : Type}

/-! ## The congruence -/

theorem modEq_list_sum {β : Type} (L : List β) (f g : β → ℤ) (n : ℤ) (h : ∀ b ∈ L, f b ≡ g b [ZMOD n]) :
    (L.map f).sum ≡ (L.map g).sum [ZMOD n] := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h b List.mem_cons_self).add (ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

/-! ## The occurrence bound -/

/-! ## Recovery (P3:1965-1982) -/

end NearCubicWires.WireExponent3_5.Compiler
