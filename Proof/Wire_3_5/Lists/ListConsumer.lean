import Proof.Wire_3_5.Lists.ListFlatten

/-! # Consumer check: the amplified lists in `row:sym-reported` (P3:2467-2502)

Checks the `list:flatten` contract against its consumer, the symmetric-top rows (P3:2467-2502): "Use the repaired
amplified lists of Lemmas list:repair and list:flatten, at population cap a fixed multiple of `B`. For every source
seed `e` they report one value for each `s_j^±` [...] Write `H_{e,τ}(z,u,v)` for their joint state indicator [...]
Pointwise, `H_{e,τ} ∈ {0,1}`, `Σ_τ H_{e,τ} = 1` [...] The reported Boolean conjunction is
`R̂_e(z,u,v) = Σ_τ H_{e,τ}(z,u,v) Π_j g_j(A_{j,z}(u)+B_{j,z}(v)+t_j^+−t_j^−)`. It is a bit on every input and seed. If all
lists report correctly, it equals the original conjunction, whatever values the one-sided scores have. Thus list
correctness controls the entire selected lookup, with no multiplication of its failure probability by the number of
states."

Main quantities: the joint state `jointState e` of `a` circuits' residual counts `s_j^±` (one amplified list per
count, one common seed `e`), the reported conjunction `reportedSym` and the true one `trueSym` for arbitrary lookups
`g_j` and one-sided scores `A_j + B_j`. Results: `jointState_exactlyOne` (`Σ_τ H_{e,τ} = 1` on every seed and input),
`reportedSym_eq_of_correct` (correct lists give the true conjunction for every score), and **`reportedSym_fail_le`**
(`Pr_e[R̂_e ≠ R] ≤ 2a·2^{−errExp}` when every population is at most the cap: `2a` list failures, not one per state). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Lists
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open Finset

namespace FlatListParams
variable (P : FlatListParams) {a : ℕ}

/-- The joint reported state `τ = (t_1^+, t_1^−, …, t_a^+, t_a^−)` at seed `e`. -/
def jointState (Zp Zm : Fin a → List Bool) (e : P.FlatSeed) : Fin a → ℕ × ℕ :=
  fun j => (P.flatReport e (Zp j), P.flatReport e (Zm j))

/-- The original conjunction `Π_j g_j(A_j + B_j + s_j^+ − s_j^−)` (`row:identity`, P3:2458-2460). -/
def trueSym (g : Fin a → ℤ → Bool) (score : Fin a → ℤ) (Zp Zm : Fin a → List Bool) : Bool :=
  decide (∀ j, g j (score j + (Zp j).count true - (Zm j).count true) = true)

end FlatListParams

end NearCubicWires.WireExponent3_5.Lists
