import Proof.Wire_3_5.Filters.FilterSoft

/-! # `filt:soft` and `filt:observable` at the seed's filters and the concentrated hash (P3:2205-2383)

Instantiates the abstract soft-mask lemma (`Proof.Wire_3_5.Filters.FilterSoft`) with the objects the paper names
(P3:2208-2218): "Let `F_reg` be Lemma filt:gap's filter with threshold `B` and error `ξ_reg=n^{−D_reg}`. Let `F_aux` use
threshold `CB` and error `ε_aux=2^{−D_aux L²}`. Their respective completeness/soundness ranges are `[0,B]` and
`[CB,∞)`, `[0,CB]` and `[C²B,∞)`." Both filters are the seed's `gapFilter` (`C = 4096`); the count hash and its majorant
are `filt:majorant`'s (`MajorantParams`); the seed of the hash is coded by its `2t·ℓ₀` basis bits (`seedCode`), on which
the greedy method of conditional expectations runs bit by bit ("using at most two printer calls per hash bit",
P3:2332-2334).

Main results: **`soft_hash`** (P3:2224-2226: the greedy hash `h_*` has `E_x 1[w(x) ≤ CB]·1[some included count list is
incorrect under h_*] ≤ (A(B_*2^{−J}+J·8^{−2t}) + ε_aux·A(M+J·M^{2t}))/(1−ε_aux)`, i.e. `≤ 4ξ_base` once the two error
terms are at most `ξ_base` and `ε_aux ≤ 1/2`), **`observable`** (P3:2362-2366: `E_{x,e}F_reg(e,x)|R̂(x)−R(x)| ≤ that +
ξ_reg` for every row lookup whose reported value agrees with the true one when every list is correct), and the common
scale (P3:2273-2276): **`H_mul_prod_W`** (`H_h(x)·Π_{j<J}W_j^{2t}` is a natural number, so `Δ₀ = 2^{s_h}Π_jW_j^{2t}`
clears every conditional objective's denominator). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces Finset

namespace MajorantParams
variable (P : MajorantParams)

/-- The hash seed's binary code: `2t` field coefficients, each by its `ℓ₀` basis coordinates. -/
noncomputable def seedCode : (Fin (2 * P.t * P.ell0) → Bool) ≃ P.Seed :=
  (Equiv.arrowCongr (finProdFinEquiv.symm) (Equiv.refl Bool)).trans <|
    (Equiv.curry (Fin (2 * P.t)) (Fin P.ell0) Bool).trans <|
      Equiv.arrowCongr (Equiv.refl _) <|
        (Equiv.arrowCongr (Equiv.refl (Fin P.ell0)) finTwoEquiv.symm).trans P.coord.toEquiv.symm

/-! ## The common scale (P3:2273-2276) -/

/-! ## The instance -/

variable {X : Type} [Fintype X] [Nonempty X]

theorem booleanMean_eq_uMean {Ω : Type} [Fintype Ω] (f : Ω → Bool) : booleanMean f = uMean fun ω => bitR (f ω) := rfl

theorem booleanMean_not {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → Bool) :
    booleanMean (fun ω => !f ω) = 1 - booleanMean f := by
  unfold booleanMean
  have hc : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hc.ne', ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun ω _ => show bitAsReal (!f ω) + bitAsReal (f ω) = 1 by cases f ω <;> simp [bitAsReal])]
  simp

/-- **`filt:soft` at the concentrated hash** (P3:2220-2231). The inputs `x` carry the filters' residual vector `zres x`
(its weight is `w(x)`) and the included count populations `pops x`; the auxiliary filter is the seed's `gapFilter` at
cap `CB` (`Paux.cap`) with error `ε_aux = 2^{−Paux.errExp}`. If every population is within the hash's range at every
input of weight at most `C²B = 4096·Paux.cap`, then the greedy hash `h_*` has
`E_x 1[w ≤ CB]·1[some list wrong under h_*] ≤ (A(B_*2^{−J} + J·8^{−2t}) + ε_aux·A(M + J·M^{2t}))/(1 − ε_aux)`. -/
theorem soft_hash (spectrum : ExpanderSpectrumContract) (Paux : GapParams) (hauxU : 1 ≤ Paux.cap)
    (hauxE : 1 ≤ Paux.errExp) (zres : X → List Bool) (hzlen : ∀ x, (zres x).length ≤ Paux.len)
    (pops : X → List (List Bool)) (ht : 1 ≤ P.t) (hA : ∀ x, (pops x).length ≤ P.A)
    (hM : ∀ x, ∀ Z ∈ pops x, Z.length ≤ P.M)
    (hlow : ∀ x, (zres x).count true ≤ 4096 * Paux.cap → ∀ Z ∈ pops x, (P.active Z).card ≤ P.Bstar) :
    let hstar := P.seedCode (greedy (2 * P.t * P.ell0) fun s =>
      softObjective (fun e x => gapFilter Paux e (zres x)) (fun h x => P.H (pops x) h) (P.seedCode s))
    uMean (fun x => bitR (decide ((zres x).count true ≤ Paux.cap) &&
        decide (∃ Z ∈ pops x, (P.data hstar).listReport Z ≠ Z.count true))) ≤
      (P.A * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t) +
        (1 / 2 ^ Paux.errExp) * (P.A * (P.M + P.J * (P.M : ℝ) ^ (2 * P.t)))) / (1 - 1 / 2 ^ Paux.errExp) := by
  intro hstar
  have hG := gapFilter_guarantee spectrum Paux hauxU
  have hε1 : (1 : ℝ) / 2 ^ Paux.errExp < 1 := by
    rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by norm_num) (by omega)
  have hH0 : ∀ h x, 0 ≤ P.H (pops x) h := fun h x => P.H_nonneg _ h
  have hHmax : ∀ h x, P.H (pops x) h ≤ P.A * (P.M + P.J * (P.M : ℝ) ^ (2 * P.t)) := by
    intro h x
    refine (P.H_le_max (pops x) (hM x) h).trans ?_
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hA x) (by positivity)
  have hlowH : ∀ x, (zres x).count true ≤ 4096 * Paux.cap →
      uMean (fun h => P.H (pops x) h) ≤ P.A * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t) := by
    intro x hx
    have := P.sum_H_le ht (pops x) (fun Z hZ => ⟨hM x Z hZ, hlow x hx Z hZ⟩)
    unfold uMean
    have hS : (0 : ℝ) < Fintype.card P.Seed := Nat.cast_pos.mpr Fintype.card_pos
    rw [div_le_iff₀ hS]
    have hlen : ((pops x).length : ℝ) ≤ P.A := by exact_mod_cast hA x
    have hnn : (0 : ℝ) ≤ P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t := by positivity
    calc ∑ h, P.H (pops x) h
        ≤ Fintype.card P.Seed * ((pops x).length * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t)) := this
      _ ≤ Fintype.card P.Seed * (P.A * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t)) := by gcongr
      _ = P.A * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t) * Fintype.card P.Seed := by ring
  have hhigh : ∀ x, 4096 * Paux.cap < (zres x).count true →
      auxMean (fun e x => gapFilter Paux e (zres x)) x ≤ 1 / 2 ^ Paux.errExp := by
    intro x hx
    unfold auxMean
    rw [← booleanMean_eq_uMean]
    exact hG.sound (zres x) (hzlen x) hx.le
  have hcomp : ∀ x, (zres x).count true ≤ Paux.cap →
      1 - 1 / 2 ^ Paux.errExp ≤ auxMean (fun e x => gapFilter Paux e (zres x)) x := by
    intro x hx
    unfold auxMean
    rw [← booleanMean_eq_uMean]
    have := hG.complete (zres x) (hzlen x) hx
    rw [booleanMean_not] at this
    linarith
  exact filt_soft (fun e x => gapFilter Paux e (zres x)) (fun h x => P.H (pops x) h) (fun x => (zres x).count true)
    Paux.cap (4096 * Paux.cap) ((P.A : ℝ) * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t))
    (1 / 2 ^ Paux.errExp) ((P.A : ℝ) * (P.M + P.J * (P.M : ℝ) ^ (2 * P.t))) (by positivity) (by positivity) hε1
    hH0 hHmax hlowH hhigh hcomp
    (fun h x => decide (∃ Z ∈ pops x, (P.data h).listReport Z ≠ Z.count true))
    (fun h x hE => by
      simp only [decide_eq_true_eq] at hE
      obtain ⟨Z, hZ, hne⟩ := hE
      apply P.H_dominates ht (pops x) h Z hZ
      intro hgood
      exact hne ((P.data h).listReport_eq_count (P.inLevel_zero h) (P.inLevel_nest h) Z (hM x Z hZ) hgood))
    P.seedCode

end MajorantParams

end NearCubicWires.WireExponent3_5.Filters
