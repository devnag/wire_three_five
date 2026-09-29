import Proof.Wire_3_5.Compiler.Polarization
import Proof.CaseAnalysis.FinalPrinterMonomials

/-! # Substituting the disjoint exact children, with cancellation (`alg:compiler`, P3:1924-1929, 1939-1946)

Realizes the substitution step of the proof of `alg:compiler`: "Substitute the disjoint exact children in each
polynomial over `𝔽₂`. This linear substitution preserves degree. Reducing squares and cancelling repeated monomials
leaves at most `Σ_{j=0}^{min(d,P_ex)} C(P_ex, j) ≤ (P_ex+1)^d` monomials" (P3:1924-1929), with the disjoint exact
children of `alg:disjoint`/`alg:pullback` ("`H(x) = Σ_j 1[E_j(x)=0]` on the Boolean cube, with the sum always in
`{0,1}` [...] Disjointness is essential: the displayed integer sum is also the sum over `𝔽₂`", P3:1605-1617).

Atoms of type `α` have child labels `children a : List ℕ`; a child label's value is a Boolean `x c`. A child polynomial is
a `Finset (Finset ℕ)`: the supports (sets of child labels, squares reduced) whose monomial occurs an odd number of times
(repeated monomials cancelled). `ChildPoly.eval` is the parity of the supports all of whose children hold.

Main declarations: `monoSupports`, `xorCanon`, **`substitute`** (the ref), `ChildPoly.eval`; **`substitute_eval`** (exact:
the substituted polynomial has the atom polynomial's value, for exact children); `substitute_subset` (supports lie in the
pool, of size `≤ d`) and **`substitute_card_le`** (`≤ Σ_{j≤d} C(P_ex, j) ≤ (P_ex+1)^d`); `listSupports` (a computable
canonical listing of a child polynomial, `Finset.equivBitIndices` order), with `listSupports_nodup`, `mem_listSupports`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

variable {α : Type}

/-! ## Exactness -/

theorem bitZ_xor (a b : Bool) : bitZ (xor a b) = (bitZ a + bitZ b) % 2 := by
  cases a <;> cases b <;> decide

theorem F2Poly.eval_eq_xorAll (p : F2Poly α) (ρ : α → Bool) :
    F2Poly.eval p ρ = xorAll (p.map fun m => m.all ρ) := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    have := F2Poly.eval_append [m] p ρ
    simp only [List.singleton_append] at this
    rw [this, ih]
    simp [F2Poly.eval, xorAll]

/-! ## The monomial count -/

theorem card_powerset_filter_le (pool : Finset ℕ) (d : ℕ) :
    (pool.powerset.filter fun S => S.card ≤ d).card ≤ (pool.card + 1) ^ d := by
  calc (pool.powerset.filter fun S => S.card ≤ d).card
      ≤ ((Finset.range (d + 1)).biUnion fun j => pool.powersetCard j).card := by
        apply Finset.card_le_card
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
        exact ⟨S.card, by omega, hS.1, rfl⟩
    _ ≤ ∑ j ∈ Finset.range (d + 1), (pool.powersetCard j).card := Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (d + 1), pool.card.choose j := by simp [Finset.card_powersetCard]
    _ ≤ (pool.card + 1) ^ d := RepairSource.CloseoutFinal.C10PrinterMonomials.sum_choose_le_succ_pow _ _

/-! ## A canonical listing -/

end NearCubicWires.WireExponent3_5.Compiler
