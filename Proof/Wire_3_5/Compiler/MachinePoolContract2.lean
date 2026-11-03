import Proof.Wire_3_5.Compiler.MachinePoolRunCost
import Proof.Wire_3_5.Compiler.MachinePoolContract

/-! # C3a′: the pool builder's contract with the hypotheses its machine needs (P3:1596-1664, 1896-1906)

Paper: alg:disjoint, "There is an explicitly constructible list of at most `max(1, fℓ)` integer affine equations
`E_j(x) = 0` [...] Their coefficients and targets have `O(ℓ + log(f+2))` bits. Construction is polynomial in the
explicit output size" (P3:1604-1615); alg:pullback in the star instance, "For a common pool over all `2^k` rows and
polynomially many original atoms, it gives `P_ex ≤ 2^k n^{O(1)}`" (P3:1661-1664); and "all displayed logarithmic and
degree parameters are bounded by fixed polynomials in `n`" (P3:1896-1897).

MC6's C3a contract (`c3a`) writes every dense child's P/N parts in `h` bits (`binary h`, which truncates); its
machine (`pool_run`) normalizes only children whose coefficients fit in `h` bits. The decision on T7: **`c3ap`** is
`c3a` with the precondition `R.Pre ∧ |input| ≤ 2^Ψ ∧ CoefFit ∧ LoadA aPar`:
* **`CoefFit`** (P3:1612-1613: the children's coefficients and targets have `O(ℓ + log(f+2))` bits, so the consumer
  picks `h` polynomially large): every weight and target of every exact child of every pool gate is below `2^h`;
* **`LoadA`**: `1 ≤ n` and `1 ≤ h` (the children's coefficients are written in `h ≥ 1` bits); the dense width, `h`, `Q'` and the number of pool gates (P3:1662-1663, "polynomially many
  original atoms") within `(n+1)^{a_par}` (P3:1896-1897); every gate's decomposition request (arity and description)
  within `(n+1)^{a_par}` (alg:disjoint's input, P3:1598-1601), so the decomposition's own budget
  `a.coefficient·(arity + bits + 1)^{a.degree}` is polynomial with degree `a.degree·a_par`; and the pool's size within
  the class argument, `|flips|·(B + 1) ≤ 2^Ψ` (P3:1661-1664, `P_ex = |flips|·B`).
The reference, output, class and error field are MC6's (`c3ap_err` is `c3a_err`). The machine's input word is the
record `c3aFields` (the decomposition's request stream and layout constants, the pool builder's constants, the unary
counts). The paper quantities are alg:disjoint's and alg:pullback's hypotheses. Main declarations: `CoefFit`, `LoadA`,
**`c3ap`**, **`c3ap_err`**, **`c3ap_not_nil`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost

variable (a : DecompositionAlgorithm)

/-- **The children's coefficients fit in `h` bits** (alg:disjoint, P3:1612-1613). -/
def CoefFit (R : PoolReq) : Prop :=
  ∀ g ∈ R.gates, ∀ e ∈ children a g, ∀ z ∈ List.ofFn e.weight ++ [e.target], z.natAbs < 2 ^ R.h


end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
