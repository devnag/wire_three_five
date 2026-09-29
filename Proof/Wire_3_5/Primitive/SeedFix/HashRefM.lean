import Proof.Wire_3_5.Primitive.SeedFix.HashRef

/-! # C4.Hb, reference in the machine's order: one term per odometer cell (`filt:soft`, P3:2253-2290)

"Expand each `A`-product into at most `2^{2t}` signed products of hash prefix indicators [...] After fixing `p`,
Gaussian elimination finds its conditional probability [...] The terminal counts are handled in the same way"
(P3:2262-2272). The Hb machine walks an odometer over `(q, e, p, λ, ι, γ)`: the star row, the aux seed, the population,
the level `λ ≤ J` (`λ = J` is the terminal count), the moment tuple `ι` of `ℓ₀`-bit positions and the sign pattern
`γ`. Every HASH row is a FILTER row, one term with one factor (`filtRefC`), so the cell prints at most ONE term:
`(W·c, F_{q,e} :: [Z_{ι_r}]_r)`, with
* `c` the Gaussian-elimination count of the cell's constraints `(ι_r, low_{λ+1} = γ_r·2^λ)` (at the terminal level the
  constraints `(ι_r, low_J = 0)`, all equal),
* `W` the cleared weight `clearW λ·(−1)^{#γ=0}` (moments) or `prodW` (terminal),
* printed only when the cell is valid (every `ι_r` a position of the population; at the terminal level `γ = 0` and `ι`
  constant) and `c ≠ 0`.
The terminal term's `2t` equal factors `Z_i` have the value of `Z_i` (a bit), and repeated equations do not change the
count ("Repeated labels and repeated equations are allowed", P3:2270-2271).

Paper quantity of the main type (**`hashTermsM_eval`**): the printed column value `Σ_q Σ_e F·Σ_pop hashElimZ`, `hashSum` summand, as `hashTerms_eval`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.HashB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.SeedFix NearCubicWires.WireExponent3_5.Filters
open Finset

section Cells
variable (MP : MajorantParams)

/-- The cell's population (`(false, [])` past the end). -/
def popOf (pops : List (Bool × List ℕ)) (p : ℕ) : Bool × List ℕ := pops.getD p (false, [])

/-- The cell's constraint width: `λ + 1` at a moment level, `J` at the terminal level. -/
def kOf (lam : ℕ) : ℕ := if lam < MP.J then lam + 1 else MP.J

/-- The cell's constraints `(ι_r, γ_r·2^λ)` (all values `0` at the terminal level). -/
def consOf (lam : ℕ) (ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0)) (γ : Fin (2 * MP.t) → Bool) : List (ℕ × ℕ) :=
  (List.finRange (2 * MP.t)).map fun r => ((ι r : ℕ), if lam < MP.J ∧ γ r = true then 2 ^ lam else 0)

/-- The cell's cleared weight. -/
def wOf (lam : ℕ) (γ : Fin (2 * MP.t) → Bool) : ℤ := if lam < MP.J then (clearW MP lam : ℤ) * sgnG γ else (prodW MP : ℤ)

/-- The cell is valid: its positions lie in the population, and at the terminal level `γ = 0` and `ι` is constant. -/
def validOf (L lam : ℕ) (ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0)) (γ : Fin (2 * MP.t) → Bool) : Prop :=
  (∀ r, (ι r : ℕ) < L) ∧ (lam = MP.J → (∀ r, γ r = false) ∧ ∀ r s, ι r = ι s)

instance (L lam : ℕ) (ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0)) (γ : Fin (2 * MP.t) → Bool) :
    Decidable (validOf MP L lam ι γ) := by unfold validOf; infer_instance

/-- **The cell's term**: at most one term, `(W·c, F_{q,e} :: [Z_{ι_r}]_r)`. -/
def hcell (G : ℕ) (F : F2Poly ℕ) (q : ℕ) (pop : Bool × List ℕ) (plen pre lam : ℕ)
    (ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0)) (γ : Fin (2 * MP.t) → Bool) : SExpr :=
  if validOf MP pop.2.length lam ι γ ∧ cntG MP (kOf MP lam) plen pre (consOf MP lam ι γ) ≠ 0 then
    [(wOf MP lam γ * (cntG MP (kOf MP lam) plen pre (consOf MP lam ι γ) : ℤ),
      F :: List.ofFn fun r => zPoly G q pop.1 (pop.2.getD (ι r) 0))]
  else []

/-- **The printed expression in the machine's order**: rows `q < N²`, aux seeds `e < nE`, populations, levels
`λ ≤ J`, moment tuples `ι` and sign patterns `γ` (base-`2^{ℓ₀}` and base-`2` digit vectors, counter order). -/
def hashTermsM (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ)) (plen pre : ℕ) : SExpr :=
  (List.range (N ^ 2)).flatMap fun q => (List.range nE).flatMap fun e => (List.range pops.length).flatMap fun p =>
    (List.range (MP.J + 1)).flatMap fun lam => (digitsF (2 ^ MP.ell0) (2 * MP.t)).flatMap fun ι =>
      (digitsF 2 (2 * MP.t)).flatMap fun γ' =>
        hcell MP G (Fs.getD (q * nE + e) []) q (popOf pops p) plen pre lam ι fun r => finTwoEquiv (γ' r)

end Cells

/-! ## The value of a cell -/

section Value
variable (MP : MajorantParams)

theorem eval_hcell (G : ℕ) (F : F2Poly ℕ) (q : ℕ) (pop : Bool × List ℕ) (plen pre lam : ℕ)
    (ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0)) (γ : Fin (2 * MP.t) → Bool) (ρ : ℕ → Bool) :
    IntExpression.eval (hcell MP G F q pop plen pre lam ι γ) ρ =
      if validOf MP pop.2.length lam ι γ then
        wOf MP lam γ * (cntG MP (kOf MP lam) plen pre (consOf MP lam ι γ) : ℤ) *
          (bitZ (F2Poly.eval F ρ) * ∏ r, bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.getD (ι r) 0)) ρ))
      else 0 := by
  unfold hcell
  by_cases hv : validOf MP pop.2.length lam ι γ
  · by_cases hc : cntG MP (kOf MP lam) plen pre (consOf MP lam ι γ) = 0
    · rw [if_neg (fun h => h.2 hc), if_pos hv, seval_nil, hc]; simp
    · rw [if_pos ⟨hv, hc⟩, if_pos hv, eval_single, List.map_cons, List.prod_cons, List.map_ofFn, List.prod_ofFn]
      simp only [Function.comp_def]
  · rw [if_neg (fun h => hv h.1), if_neg hv, seval_nil]

/-- The positions below `L` of `ℓ₀`-bit moment tuples are the tuples of positions. -/
theorem sum_restrict {r L M : ℕ} (hLM : L ≤ M) (h : (Fin r → Fin M) → ℤ) :
    ∑ ι : Fin r → Fin M, (if ∀ k, (ι k : ℕ) < L then h ι else 0) =
      ∑ ι' : Fin r → Fin L, h (fun k => Fin.castLE hLM (ι' k)) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun ι hι k => ⟨ι k, (Finset.mem_filter.mp hι).2 k⟩)
    (fun ι' _ k => Fin.castLE hLM (ι' k)) (fun _ _ => Finset.mem_univ _) (fun ι' _ => ?_) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun ι hι => ?_)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k => (ι' k).isLt⟩
  · rfl

/-- A sum over the constant tuples below `L`. -/
theorem sum_const {r L M : ℕ} (hr : 0 < r) (hLM : L ≤ M) (h : (Fin r → Fin M) → ℤ) :
    ∑ ι : Fin r → Fin M, (if (∀ k, (ι k : ℕ) < L) ∧ ∀ k s, ι k = ι s then h ι else 0) =
      ∑ i : Fin L, h (fun _ => Fin.castLE hLM i) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun ι hι => ⟨ι ⟨0, hr⟩, (Finset.mem_filter.mp hι).2.1 _⟩)
    (fun i _ _ => Fin.castLE hLM i) (fun _ _ => Finset.mem_univ _) (fun i _ => ?_) (fun ι hι => ?_)
    (fun _ _ => rfl) (fun ι hι => ?_)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => i.isLt, fun _ _ => rfl⟩
  · funext k; exact ((Finset.mem_filter.mp hι).2.2 ⟨0, hr⟩ k)
  · congr 1; funext k; exact ((Finset.mem_filter.mp hι).2.2 k ⟨0, hr⟩)

theorem bitZ_pow (b : Bool) (m : ℕ) (hm : 0 < m) : bitZ b ^ m = bitZ b := by
  cases b
  · simp [bitZ, zero_pow (Nat.pos_iff_ne_zero.mp hm)]
  · simp [bitZ]

/-- Repeated terminal equations: `2t` copies of `(i, low_J = 0)` have the count of one. -/
theorem cntG_rep (plen pre i : ℕ) (hi : i < 2 ^ MP.ell0) (ht : 1 ≤ MP.t) (hplen : plen ≤ 2 * MP.t * MP.ell0)
    (γ : Fin (2 * MP.t) → Bool) :
    cntG MP MP.J plen pre (consOf MP MP.J (fun _ => ⟨i, hi⟩) γ) = cntG MP MP.J plen pre [(i, 0)] := by
  have hJ : MP.J ≤ MP.ell0 := (MajorantParams.J_lt_ell0 MP).le
  have hmem : ∀ c, c ∈ consOf MP MP.J (fun _ => ⟨i, hi⟩) γ ↔ c = (i, 0) := by
    intro c
    simp only [consOf, lt_irrefl, false_and, if_false, List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · rintro rfl; exact ⟨⟨0, by omega⟩, rfl⟩
  have hb : ∀ c ∈ consOf MP MP.J (fun _ => ⟨i, hi⟩) γ, c.1 < 2 ^ MP.ell0 ∧ c.2 < 2 ^ MP.J := by
    intro c hc; rw [(hmem c).mp hc]; exact ⟨hi, by positivity⟩
  have hb1 : ∀ c ∈ [(i, 0)], c.1 < 2 ^ MP.ell0 ∧ c.2 < 2 ^ MP.J := by
    intro c hc; rw [List.mem_singleton.mp hc]; exact ⟨hi, by positivity⟩
  have e1 := cntG_eq MP MP.J plen pre _ hJ hplen hb
  have e2 := cntG_eq MP MP.J plen pre [(i, 0)] hJ hplen hb1
  have key : (cntG MP MP.J plen pre (consOf MP MP.J (fun _ => ⟨i, hi⟩) γ) : ℤ) = (cntG MP MP.J plen pre [(i, 0)] : ℤ) := by
    rw [e1, e2]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    apply propext
    constructor
    · intro h c hc; exact h c ((hmem c).mpr (List.mem_singleton.mp hc))
    · intro h c hc; exact h c (List.mem_singleton.mpr ((hmem c).mp hc))
  exact_mod_cast key

end Value

/-! ## The sums of a population's cells -/

section Blocks
variable (MP : MajorantParams)

/-- The moment level `j < J`: the cells of `(j, ι, γ)` sum to `F·clearW_j·Σ_ι Π Z_{ι_r}·Σ_γ sgn·cnt`. -/
theorem sumB (G : ℕ) (F : F2Poly ℕ) (q : ℕ) (pop : Bool × List ℕ) (plen pre j : ℕ) (hj : j < MP.J)
    (hL : pop.2.length ≤ 2 ^ MP.ell0) (ρ : ℕ → Bool) :
    ∑ ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0), ∑ γ' : Fin (2 * MP.t) → Fin 2,
        IntExpression.eval (hcell MP G F q pop plen pre j ι fun r => finTwoEquiv (γ' r)) ρ =
      bitZ (F2Poly.eval F ρ) * ((clearW MP j : ℤ) * ∑ ι : Fin (2 * MP.t) → Fin pop.2.length,
        (∏ r, bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.get (ι r))) ρ)) *
          ∑ γ : Fin (2 * MP.t) → Bool, sgnG γ * (cntG MP (j + 1) plen pre (momentCons MP j ι γ) : ℤ)) := by
  have hne : j ≠ MP.J := Nat.ne_of_lt hj
  have hv : ∀ ι γ, validOf MP pop.2.length j ι γ ↔ ∀ r, (ι r : ℕ) < pop.2.length := by
    intro ι γ; unfold validOf; simp [hne]
  have step1 : ∀ ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0),
      ∑ γ' : Fin (2 * MP.t) → Fin 2, IntExpression.eval (hcell MP G F q pop plen pre j ι fun r => finTwoEquiv (γ' r)) ρ =
        if ∀ r, (ι r : ℕ) < pop.2.length then
          ∑ γ : Fin (2 * MP.t) → Bool, wOf MP j γ * (cntG MP (kOf MP j) plen pre (consOf MP j ι γ) : ℤ) *
            (bitZ (F2Poly.eval F ρ) * ∏ r, bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.getD (ι r) 0)) ρ))
        else 0 := by
    intro ι
    simp only [eval_hcell]
    rw [sum_signsF (fun γ => if validOf MP pop.2.length j ι γ then wOf MP j γ *
      (cntG MP (kOf MP j) plen pre (consOf MP j ι γ) : ℤ) * (bitZ (F2Poly.eval F ρ) *
        ∏ r, bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.getD (ι r) 0)) ρ)) else 0)]
    by_cases h : ∀ r, (ι r : ℕ) < pop.2.length
    · rw [if_pos h]; exact Finset.sum_congr rfl fun γ _ => by rw [if_pos ((hv ι γ).mpr h)]
    · rw [if_neg h]; exact Finset.sum_eq_zero fun γ _ => by rw [if_neg (fun h' => h ((hv ι γ).mp h'))]
  rw [Finset.sum_congr rfl fun ι _ => step1 ι, sum_restrict hL]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  have hk : kOf MP j = j + 1 := by unfold kOf; simp [hj]
  have hc : ∀ γ, consOf MP j (fun k => Fin.castLE hL (ι k)) γ = momentCons MP j ι γ := by
    intro γ; unfold consOf momentCons; simp [hj]
  have hw : ∀ γ, wOf MP j γ = (clearW MP j : ℤ) * sgnG γ := by intro γ; unfold wOf; simp [hj]
  have hg : ∀ r, pop.2.getD ((Fin.castLE hL (ι r) : Fin (2 ^ MP.ell0)) : ℕ) 0 = pop.2.get (ι r) := by
    intro r; simp [List.getD_eq_getElem, List.get_eq_getElem]
  simp only [hk, hc, hw, hg]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- The terminal level `J`: the cells sum to `F·prodW·Σ_i Z_i·cnt_i`. -/
theorem sumA (G : ℕ) (F : F2Poly ℕ) (q : ℕ) (pop : Bool × List ℕ) (plen pre : ℕ) (ht : 1 ≤ MP.t)
    (hplen : plen ≤ 2 * MP.t * MP.ell0) (hL : pop.2.length ≤ 2 ^ MP.ell0) (ρ : ℕ → Bool) :
    ∑ ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0), ∑ γ' : Fin (2 * MP.t) → Fin 2,
        IntExpression.eval (hcell MP G F q pop plen pre MP.J ι fun r => finTwoEquiv (γ' r)) ρ =
      bitZ (F2Poly.eval F ρ) * ((prodW MP : ℤ) * ∑ i : Fin pop.2.length,
        bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.get i)) ρ) * (cntG MP MP.J plen pre [((i : ℕ), 0)] : ℤ)) := by
  have hpos : 0 < 2 * MP.t := by omega
  have step1 : ∀ ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0),
      ∑ γ' : Fin (2 * MP.t) → Fin 2,
          IntExpression.eval (hcell MP G F q pop plen pre MP.J ι fun r => finTwoEquiv (γ' r)) ρ =
        if (∀ r, (ι r : ℕ) < pop.2.length) ∧ ∀ r s, ι r = ι s then
          wOf MP MP.J (fun _ => false) * (cntG MP (kOf MP MP.J) plen pre (consOf MP MP.J ι fun _ => false) : ℤ) *
            (bitZ (F2Poly.eval F ρ) * ∏ r, bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.getD (ι r) 0)) ρ))
        else 0 := by
    intro ι
    simp only [eval_hcell]
    rw [sum_signsF (fun γ => if validOf MP pop.2.length MP.J ι γ then wOf MP MP.J γ *
      (cntG MP (kOf MP MP.J) plen pre (consOf MP MP.J ι γ) : ℤ) * (bitZ (F2Poly.eval F ρ) *
        ∏ r, bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.getD (ι r) 0)) ρ)) else 0)]
    rw [Finset.sum_eq_single (fun _ => false)]
    · have e : validOf MP pop.2.length MP.J ι (fun _ => false) ↔
          (∀ r, (ι r : ℕ) < pop.2.length) ∧ ∀ r s, ι r = ι s := by
        unfold validOf; simp
      by_cases h : (∀ r, (ι r : ℕ) < pop.2.length) ∧ ∀ r s, ι r = ι s
      · rw [if_pos (e.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (e.mp h')), if_neg h]
    · intro γ _ hγ
      have hn : ¬ validOf MP pop.2.length MP.J ι γ := by
        intro hv
        apply hγ
        funext r
        exact (hv.2 rfl).1 r
      rw [if_neg hn]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun ι _ => step1 ι, sum_const hpos hL]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hk : kOf MP MP.J = MP.J := by unfold kOf; simp
  have hw : wOf MP MP.J (fun _ => false) = (prodW MP : ℤ) := by unfold wOf; simp
  have hci : cntG MP MP.J plen pre (consOf MP MP.J (fun _ => Fin.castLE hL i) fun _ => false) =
      cntG MP MP.J plen pre [((i : ℕ), 0)] :=
    cntG_rep MP plen pre i (lt_of_lt_of_le i.isLt hL) ht hplen _
  have hg : pop.2.getD ((Fin.castLE hL i : Fin (2 ^ MP.ell0)) : ℕ) 0 = pop.2.get i := by
    simp [List.getD_eq_getElem, List.get_eq_getElem]
  have hp : ∏ _r : Fin (2 * MP.t), bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.get i)) ρ) =
      bitZ (F2Poly.eval (zPoly G q pop.1 (pop.2.get i)) ρ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; exact bitZ_pow _ _ hpos
  rw [hk, hw, hci]
  simp only [hg]
  rw [hp]
  ring

/-- **One population at one row and aux seed**: its cells sum to `F·hashElimZ`. -/
theorem sum_block (G : ℕ) (F : F2Poly ℕ) (q : ℕ) (pop : Bool × List ℕ) (plen pre : ℕ) (ht : 1 ≤ MP.t)
    (hplen : plen ≤ 2 * MP.t * MP.ell0) (hL : pop.2.length ≤ 2 ^ MP.ell0) (ρ : ℕ → Bool) :
    ∑ lam ∈ range (MP.J + 1), ∑ ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0), ∑ γ' : Fin (2 * MP.t) → Fin 2,
        IntExpression.eval (hcell MP G F q pop plen pre lam ι fun r => finTwoEquiv (γ' r)) ρ =
      bitZ (F2Poly.eval F ρ) * hashElimZ MP (popAt ρ G q pop) plen pre := by
  rw [Finset.sum_range_succ, sumA MP G F q pop plen pre ht hplen hL ρ, hashElimZ_popAt]
  rw [Finset.sum_congr rfl fun j hj => sumB MP G F q pop plen pre j (Finset.mem_range.mp hj) hL ρ]
  rw [← Finset.mul_sum]
  ring

end Blocks

/-! ## The whole expression -/

theorem sum_range_getD {α : Type} (l : List α) (d : α) (g : α → ℤ) :
    ((List.range l.length).map fun p => g (l.getD p d)).sum = (l.map g).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [List.getElem?_eq_getElem h1]

/-- **The printed expression's value is the printed column value** (P3:2285-2290), in the machine's order: at every
atom assignment `ρ` whose HASH polynomials read the aux filter bits `Fv q e`, the value is
`Σ_q Σ_e F·Σ_pop hashElimZ` (`hashSum` summand). -/
theorem hashTermsM_eval (MP : MajorantParams) (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ))
    (plen pre : ℕ) (Fv : ℕ → ℕ → Bool) (ρ : ℕ → Bool) (ht : 1 ≤ MP.t) (hplen : plen ≤ 2 * MP.t * MP.ell0)
    (hL : ∀ pop ∈ pops, pop.2.length ≤ 2 ^ MP.ell0)
    (hF : ∀ q < N ^ 2, ∀ e < nE, F2Poly.eval (Fs.getD (q * nE + e) []) ρ = Fv q e) :
    IntExpression.eval (hashTermsM MP G N nE Fs pops plen pre) ρ =
      ∑ q ∈ range (N ^ 2), ∑ e ∈ range nE,
        bitZ (Fv q e) * (pops.map fun pop => hashElimZ MP (popAt ρ G q pop) plen pre).sum := by
  unfold hashTermsM
  rw [seval_flatMap, list_sum_range]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [seval_flatMap, list_sum_range]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [seval_flatMap, ← hF q (Finset.mem_range.mp hq) e (Finset.mem_range.mp he), ← List.sum_map_mul_left]
  have hp : ∀ p ∈ List.range pops.length,
      IntExpression.eval ((List.range (MP.J + 1)).flatMap fun lam =>
        (digitsF (2 ^ MP.ell0) (2 * MP.t)).flatMap fun ι => (digitsF 2 (2 * MP.t)).flatMap fun γ' =>
          hcell MP G (Fs.getD (q * nE + e) []) q (popOf pops p) plen pre lam ι fun r => finTwoEquiv (γ' r)) ρ =
        bitZ (F2Poly.eval (Fs.getD (q * nE + e) []) ρ) * hashElimZ MP (popAt ρ G q (popOf pops p)) plen pre := by
    intro p hp
    have hpl := List.mem_range.mp hp
    have hLp : (popOf pops p).2.length ≤ 2 ^ MP.ell0 := by
      unfold popOf; rw [List.getD_eq_getElem _ _ hpl]; exact hL _ (List.getElem_mem hpl)
    rw [seval_flatMap, list_sum_range]
    rw [← sum_block MP G (Fs.getD (q * nE + e) []) q (popOf pops p) plen pre ht hplen hLp ρ]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [seval_flatMap, sum_digitsF]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [seval_flatMap, sum_digitsF]
  rw [List.map_congr_left hp]
  exact sum_range_getD pops (false, []) fun pop =>
    bitZ (F2Poly.eval (Fs.getD (q * nE + e) []) ρ) * hashElimZ MP (popAt ρ G q pop) plen pre

/-- Every printed term has `1 + 2t` factors. -/
theorem hashTermsM_uniform (MP : MajorantParams) (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ))
    (plen pre : ℕ) : ∀ t ∈ hashTermsM MP G N nE Fs pops plen pre, t.2.length = 1 + 2 * MP.t := by
  intro t ht
  unfold hashTermsM at ht
  simp only [List.mem_flatMap] at ht
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := ht
  unfold hcell at hc
  split_ifs at hc
  · rw [List.mem_singleton.mp hc]; simp; omega
  · simp at hc

end NearCubicWires.WireExponent3_5.PrimT.HashB
