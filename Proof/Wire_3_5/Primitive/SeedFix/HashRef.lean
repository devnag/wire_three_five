import Proof.Wire_3_5.Primitive.SeedFix.SeedFixHashObjective
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixSampExpr
import Proof.Wire_3_5.Compiler.MachinePoolSpec
import Proof.Wire_3_5.Stars.StarMixedScore

/-! # C4.Hb, reference: the hash fixing's printed expression (`filt:soft`, P3:2253-2290)

"Expanding a discrepancy power gives `δ_{a,j}^{2t} = Σ Z_{a,i_1}⋯Z_{a,i_{2t}} A_{i_1,j}⋯A_{i_{2t},j}` [...] Expand each
`A`-product into at most `2^{2t}` signed products of hash prefix indicators [...] After fixing `p`, Gaussian elimination
finds its conditional probability [...] The terminal counts are handled in the same way. [...] At prefix `p` print
`V_p(z) = Δ₀Σ_yΣ_e F_aux(e,x(y,z))·E_h[H_h(x(y,z)) | p]`" (P3:2253-2290).

This module is the explicit integer expression that prints `V_p(z)` for `alg:compiler`. It is written over the call's
pool atoms (numbering: atom `(4·row + k)·G + gi`). For each star row `q` (`cellNum` order), aux seed `e` and
population `pop = (sgn, gis)` it has:
* the terminal terms `prodW·cnt_i · F_{q,e} · Z_i`, over the population's positions `i`;
* the moment terms `clearW_j·(−1)^{#γ=0}·cnt_{j,ι,γ} · F_{q,e} · Π_r Z_{ι_r}`, over `j < J`, `ι : Fin 2t →
  positions` and `γ : Fin 2t → Bool`.

Here `F_{q,e}` is the call's aux FILTER row at batch position `q·nE + e` (PA's HASH tape), and `Z_i` is
`Z^{sgn}` of pool gate `gis_i` at row `q` (`zPoly`, the fixed 4-atom corner form). Every count is M3's
Gaussian-elimination count `cntG`, and terms with count `0` are omitted. The terminal terms are padded with
constant-one factors to the moment terms' `1 + 2t` factors.

Paper quantity of the main type (**`hashTerms_eval`**): the printed column value `Σ_q Σ_e F·Σ_pop hashElimZ`, i.e.
`hashSum` at one column. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.HashB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.SeedFix NearCubicWires.WireExponent3_5.Filters
open Finset

/-! ## Atoms and factors -/

/-- `Z^{sgn}` of pool gate `gi` at star row `row`: the fixed corner form on the atoms `(4·row + k)·G + gi`. -/
def zPoly (G row : ℕ) (sgn : Bool) (gi : ℕ) : F2Poly ℕ :=
  (if sgn then Stars.zPlusF2 else Stars.zMinusF2).map fun m => m.map fun k => CompilerMachine.Pool.poolIndex G row k gi

/-- A population's bits at star row `row` under the atom values `ρ`. -/
def popAt (ρ : ℕ → Bool) (G row : ℕ) (pop : Bool × List ℕ) : List Bool :=
  pop.2.map fun gi => F2Poly.eval (zPoly G row pop.1 gi) ρ

theorem popAt_length (ρ : ℕ → Bool) (G row : ℕ) (pop : Bool × List ℕ) : (popAt ρ G row pop).length = pop.2.length :=
  List.length_map _

/-- Digit vectors `Fin r → Fin m` in counter order. -/
def digitsF (m r : ℕ) : List (Fin r → Fin m) := (List.finRange (m ^ r)).map finFunctionFinEquiv.symm

theorem sum_digitsF {m r : ℕ} (F : (Fin r → Fin m) → ℤ) : ((digitsF m r).map F).sum = ∑ f, F f := by
  unfold digitsF
  rw [List.map_map, ← Fin.sum_univ_def]
  exact Equiv.sum_comp finFunctionFinEquiv.symm F

theorem sum_signsF {r : ℕ} (F : (Fin r → Bool) → ℤ) :
    ∑ γ' : Fin r → Fin 2, F (fun k => finTwoEquiv (γ' k)) = ∑ γ : Fin r → Bool, F γ :=
  Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv) F

theorem list_sum_range (J : ℕ) (f : ℕ → ℤ) : ((List.range J).map f).sum = ∑ j ∈ range J, f j := by
  induction J with
  | zero => rfl
  | succ J ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The sign `(−1)^{#{γ_r = false}}`. -/
def sgnG {r : ℕ} (γ : Fin r → Bool) : ℤ := (-1 : ℤ) ^ (univ.filter fun k => γ k = false).card

theorem eval_single (c : ℤ) (fs : List (F2Poly ℕ)) (ρ : ℕ → Bool) :
    IntExpression.eval [(c, fs)] ρ = c * (fs.map fun p => bitZ (F2Poly.eval p ρ)).prod := by
  rw [seval_cons, seval_nil, add_zero]

/-! ## The terms -/

section Terms
variable (MP : MajorantParams)

/-! ## The value -/

/-- The elimination form of a population read at the atoms: the same sums, indexed by the population's positions. -/
theorem hashElimZ_popAt (ρ : ℕ → Bool) (G q plen pre : ℕ) (pop : Bool × List ℕ) :
    hashElimZ MP (popAt ρ G q pop) plen pre =
      (prodW MP : ℤ) * ∑ i : Fin pop.2.length,
        bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.get i)) ρ) * (cntG MP MP.J plen pre [((i : ℕ), 0)] : ℤ) +
      ∑ j ∈ range MP.J, (clearW MP j : ℤ) * ∑ ι : Fin (2 * MP.t) → Fin pop.2.length,
        (∏ r, bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.get (ι r))) ρ)) *
          ∑ γ : Fin (2 * MP.t) → Bool, sgnG γ * (cntG MP (j + 1) plen pre (momentCons MP j ι γ) : ℤ) := by
  have h := popAt_length ρ G q pop
  set e : Fin (popAt ρ G q pop).length ≃ Fin pop.2.length := finCongr h with he
  have hget : ∀ i : Fin (popAt ρ G q pop).length,
      (popAt ρ G q pop).get i = F2Poly.eval (zPoly G q pop.1 (pop.2.get (e i))) ρ := by
    intro i
    simp [popAt, he, List.get_eq_getElem]
    rfl
  unfold hashElimZ
  congr 1
  · congr 1
    exact Fintype.sum_equiv e _ _ fun i => by rw [hget]; rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) e) _ _ fun ι => ?_
    have hm : ∀ γ : Fin (2 * MP.t) → Bool,
        momentCons MP j ι γ = momentCons MP j ((Equiv.arrowCongr (Equiv.refl _) e) ι) γ := by
      intro γ
      simp [momentCons, he]
    simp only [hget, hm]
    rfl

end Terms

end NearCubicWires.WireExponent3_5.PrimT.HashB
