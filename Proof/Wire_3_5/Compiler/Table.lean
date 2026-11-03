import Proof.Wire_3_5.Compiler.Expression
import Proof.Wire_3_5.Compiler.Pullback
import Proof.Foundations.SupplierPrinter
import Proof.Wire_3_5.Compiler.StackLift

/-! # `alg:compiler` end to end: a pool of pulled-back threshold atoms, the printed table, and `alg:eq-budget`
(P3:1874-1964)

Realizes `alg:compiler`: "Suppose a pool of `P` pulled-back threshold atoms has the disjoint exact children of Lemma
alg:pullback, and write `P_ex` for the size of the resulting equation pool. Let `V(z)=Σ_ν c_ν ∏_j p_{ν,j}(z)` [...]
Suppose `0≤V(z)≤J` on every column, choose `Q≥1` with `2^Q>J`, and put `Q'=Q+m−1`. There is an explicit signed
separated-equation expression congruent to `2^{m−1}V(z)` modulo `2^{Q'}`, with at most
`𝒮≤A 2^m Q'(P_ex+1)^{Q'd}` occurrences. Each occurrence stacks at most `Q'd` original exact equations and has a
coefficient of `O(b+m+Q')` bits. If [...] `log₂A+m+log₂Q'+Q'd log₂(P_ex+1)≤n_out/100` (alg:eq-budget), the complete
table of `V` is recoverable exactly" (P3:1876-1908), with the proof's last steps "Under (alg:eq-budget), apply Theorem
alg:separable-printer. At each column, the least nonnegative residue is exactly `2^{m−1}V(z)`, because
`0≤2^{m−1}V(z)≤2^{m−1}J<2^{Q'}`. Divide it by `2^{m−1}`" (P3:1937-1944).

The lift precision parameter `Q` of `compileExpression` is the paper's `Q'`; the hypothesis `2^{m−1}J < 2^Q` is the
paper's `2^{m−1}J < 2^{Q'}` (implied by `2^Q > J` at `Q' = Q+m−1`). The logarithms of `alg:eq-budget` are read as
exponents: `A ≤ 2^a`, `Q' ≤ 2^q`, `P_ex+1 ≤ 2^p`, `a+m+q+Q'd·p ≤ B` gives `𝒮 ≤ 2^B` (the separable printer's
`s ≤ 2^{n_out/100}` at `B = n_out/100`).

Main declarations: `polarize_coeff_abs_le`, **`compileExpression_coeff_abs_le`** (`|coefficient| ≤ C_b·2^m·2^{Q'}`),
**`compileExpression_stack`** (every occurrence is one stacked equation of `≤ Q'd` pool labels); `recoverTable` with
**`compileExpression_table`** (the recovered, divided residue is `V`); `PulledAtom` (a threshold gate, its disjoint exact
decomposition, and its half coordinates), `poolChildren`, `poolBits` (the atom values at a column), `poolSize`
(`P_ex`), **`compilePool`** (the compiler on the pooled children); **`poolBits_exact`**, **`poolEqs_abs_le`**
(child-value envelope), **`compilePool_length_le`** (`alg:eq-occurrences`), **`occurrences_le_budget`** and
**`compilePool_budget`** (`alg:eq-budget`), and **`compilePool_table`** (the table of `V` is the recovered weighted-dominance
table of the compiled occurrences). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPrinter

variable {α ZL ZR : Type}

/-! ## Occurrence coefficients and stack sizes -/

/-! ## Recovery of the table -/

/-! ## The pool of pulled-back threshold atoms -/

/-- A pulled-back threshold atom (P3:1876-1878): a threshold gate with its disjoint exact decomposition
(`alg:disjoint`), read at a point given by half coordinates (`alg:pullback`). -/
structure PulledAtom (n : ℕ) (ZL ZR : Type) where
  coords : HalfCoords n ZL ZR
  gate : NormalizedThresholdGate n
  dec : ExactDecomposition gate

/-- The pulled-back children of every atom, in pool order. -/
def poolChildren {n : ℕ} (pool : List (PulledAtom n ZL ZR)) : List (List (SeparatedEquation ZL ZR)) :=
  pool.map fun a => pullbackChildren a.coords a.dec

end NearCubicWires.WireExponent3_5.Compiler
