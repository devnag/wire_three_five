import Proof.Wire_3_5.Rows.RowsThr

/-! # Rows: the sampler interface for the symmetric-top and threshold-top observables (P3:2721-2757)

Realizes `row:sampler-interface` (P3:2721-2743): "Let a common sample `𝒮=((U_ℓ,V_ℓ))_{ℓ=1}^Q` satisfy
`E_z max_{ρ,e,t} ‖QD_{ρ,e,t}(z) − N²Σ_ℓ D_{ρ,e,t}(z)[U_ℓ,V_ℓ]e_{U_ℓ}e_{V_ℓ}ᵀ‖_op/(QN) ≤ η`. There is a fixed polynomial
bound `𝔐=n^{O(1)}` such that replacing each live-pair average by this common sample changes the average filtered
reported observable by at most `𝔐η`. For SYM one may take `𝔐=(Π_j(m_j+1)²)(Π_j√P_j)`, and for a threshold-top
conjunction one may take `𝔐=|𝒢|max_{p∈𝒫}p`."

Paper quantities: the live-pair average `liveMean` (`E_{u,v}`), the sample average `sampleMean` (`(1/Q)Σ_ℓ`), the filtered
reported observables `symRow` (`G_e·R̂_e` of row:sym-reported) and `thrObservable` (`G·Σ_{g,p}(1/|𝒫|)R̂_{g,p}` of
row:thr-reported), the state matrices `D_{ρ,e,t} = G_e·H_{ρ,e,t}` (`stateMatrix`, row:matrix), and `𝔐`.

Results: **`sym_sampler_interface`** with `𝔐 = (Π_j(m_j+1)²)(Π_jP_j)` (F5: mass `P_j` from `|f̂_j| ≤ 1`, not
Parseval's `√P_j`; still `n^{O(1)}`, which is all the consumer uses, P3:3159), **`thr_sampler_interface`** with
`𝔐 = |𝒢|·max_p p`, and **`averaged_sample_error`** (the average over columns `z` and final seeds `e`: "Averaging its
pointwise upper bound over `z` proves the result"). Every bound holds for all one-sided selectors, including selectors
chosen after the sample and the column (P3:2757-2760). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.Shared ZMod Finset Matrix
open scoped Matrix.Norms.L2Operator

section Means
variable {N Q : ℕ}

/-- The live-pair average `E_{u,v∈[N]} f(u,v)`. -/
noncomputable def liveMean (f : Fin N → Fin N → ℝ) : ℝ := (∑ u, ∑ v, f u v) / (N : ℝ) ^ 2

/-- The sample average `(1/Q)Σ_ℓ f(U_ℓ,V_ℓ)`. -/
noncomputable def sampleMean (S : Fin Q → Fin N × Fin N) (f : Fin N → Fin N → ℝ) : ℝ :=
  (∑ l, f (S l).1 (S l).2) / Q

theorem bitR_cast (b : Bool) : ((bitR b : ℝ) : ℂ) = bitC b := by cases b <;> simp [bitR, bitC]

/-- A real row with a separable complex expansion obeys the separable sample bound. -/
theorem real_sample_error {T Λ : Type} [Fintype T] [Fintype Λ] (hN : 0 < N) (hQ : 0 < Q) (f : Fin N → Fin N → ℝ)
    (G : Fin N → Fin N → ℂ) (H : T → Fin N → Fin N → ℂ) (c : T → Λ → ℂ) (a b : Λ → Fin N → ℂ)
    (ha : ∀ lam i, ‖a lam i‖ ≤ 1) (hb : ∀ lam i, ‖b lam i‖ ≤ 1) (S : Fin Q → Fin N × Fin N) (η : ℝ)
    (hη : ∀ t, ‖sampleError (stateMatrix G H t) S‖ / (Q * N) ≤ η)
    (hf : ∀ u v, (f u v : ℂ) = separableRow G H c a b u v) :
    |liveMean f - sampleMean S f| ≤ (∑ t, ∑ lam, ‖c t lam‖) * η := by
  have h := separable_sample_error hN hQ G H c a b ha hb S η hη
  have hcast : ((liveMean f - sampleMean S f : ℝ) : ℂ) =
      (∑ u, ∑ v, separableRow G H c a b u v) / (N : ℂ) ^ 2 -
        (∑ j, separableRow G H c a b (S j).1 (S j).2) / (Q : ℂ) := by
    simp only [liveMean, sampleMean, ← hf]
    push_cast
    rfl
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem liveMean_sum {ι : Type} [Fintype ι] (w : ι → ℝ) (f : ι → Fin N → Fin N → ℝ) :
    liveMean (fun u v => ∑ i, w i * f i u v) = ∑ i, w i * liveMean (f i) := by
  unfold liveMean
  rw [show (∑ i, w i * ((∑ u, ∑ v, f i u v) / (N : ℝ) ^ 2)) = (∑ i, w i * ∑ u, ∑ v, f i u v) / (N : ℝ) ^ 2 by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring]
  congr 1
  simp only [Finset.mul_sum]
  calc ∑ u, ∑ v, ∑ i, w i * f i u v = ∑ u, ∑ i, ∑ v, w i * f i u v :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ i, ∑ u, ∑ v, w i * f i u v := Finset.sum_comm

theorem sampleMean_sum {ι : Type} [Fintype ι] (S : Fin Q → Fin N × Fin N) (w : ι → ℝ)
    (f : ι → Fin N → Fin N → ℝ) :
    sampleMean S (fun u v => ∑ i, w i * f i u v) = ∑ i, w i * sampleMean S (f i) := by
  unfold sampleMean
  rw [Finset.sum_comm]
  simp only [Finset.sum_div, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

end Means

/-! ## Symmetric tops (P3:2467-2539, 2735-2736) -/

section Sym
variable {N Q a : ℕ}

/-- The joint state alphabet `τ = (t_1^+,t_1^−,…,t_a^+,t_a^−)` with `t_j^± ∈ {0,…,m_j}` (P3:2478-2488). -/
abbrev SymState (m : Fin a → ℕ) : Type := (j : Fin a) → Fin (m j + 1) × Fin (m j + 1)

/-- "The number of states is at most `Π_j(m_j+1)²`" (P3:2487). -/
theorem card_symState (m : Fin a → ℕ) : Fintype.card (SymState m) = ∏ j, (m j + 1) ^ 2 := by
  simp [SymState, Fintype.card_pi, Fintype.card_prod, sq]

/-- The signed state shift `t_j^+ − t_j^−`. -/
def symShift (m : Fin a → ℕ) (τ : SymState m) (j : Fin a) : ℤ := ((τ j).1 : ℤ) - (τ j).2

/-- **`reportedSym`, filtered** (row:sym-reported, P3:2489-2494): `G_e(u,v)·Σ_τ H_{e,τ}(u,v)Π_j g_j(A_j(u)+B_j(v)+t_j^+−t_j^−)`
at one column and one final seed. -/
noncomputable def symRow (m : Fin a → ℕ) (g : Fin a → ℤ → Bool) (G : Fin N → Fin N → Bool)
    (H : SymState m → Fin N → Fin N → Bool) (A B : Fin a → Fin N → ℤ) (u v : Fin N) : ℝ :=
  bitR (G u v) * ∑ τ, bitR (H τ u v) * ∏ j, bitR (g j (A j u + B j v + symShift m τ j))

/-- The SYM state matrices `D_{e,τ} = G_e·H_{e,τ}` (row:matrix) as complex matrices. -/
noncomputable def symStateMatrix (m : Fin a → ℕ) (G : Fin N → Fin N → Bool) (H : SymState m → Fin N → Fin N → Bool)
    (τ : SymState m) : Fin N → Fin N → ℂ :=
  stateMatrix (fun u v => bitC (G u v)) (fun τ u v => bitC (H τ u v)) τ

/-- **`row:sampler-interface` for SYM** (P3:2721-2736, 2750-2755): with one-sided scores `A_j(u) ∈ [−m_j,m_j]` and
`B_j(v) ∈ [0,m_j]` (as in row:one-sided with coefficient one), if every state matrix has normalized sample error at most
`η`, the sampled filtered reported observable differs from its live-pair average by at most `𝔐η` with
`𝔐 = (Π_j(m_j+1)²)(Π_jP_j)`. -/
theorem sym_sampler_interface (hN : 0 < N) (hQ : 0 < Q) (m : Fin a → ℕ) (g : Fin a → ℤ → Bool)
    (G : Fin N → Fin N → Bool) (H : SymState m → Fin N → Fin N → Bool) (A B : Fin a → Fin N → ℤ)
    (hA : ∀ j u, -(m j : ℤ) ≤ A j u ∧ A j u ≤ m j) (hB : ∀ j v, 0 ≤ B j v ∧ B j v ≤ m j)
    (S : Fin Q → Fin N × Fin N) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : ∀ τ, ‖sampleError (symStateMatrix m G H τ) S‖ / (Q * N) ≤ η) :
    |liveMean (symRow m g G H A B) - sampleMean S (symRow m g G H A B)| ≤
      ((∏ j, ((m j + 1) ^ 2 : ℕ) : ℝ) * ∏ j, (symModulus (m j) : ℝ)) * η := by
  have hsep := real_sample_error hN hQ (symRow m g G H A B) (fun u v => bitC (G u v)) (fun τ u v => bitC (H τ u v))
    (fun τ ℓ => symCoeff m g (symShift m τ) ℓ) (fun ℓ u => symLeft m (fun j => A j u) ℓ)
    (fun ℓ v => symRight m (fun j => B j v) ℓ) (fun ℓ u => (norm_symLeft m _ ℓ).le)
    (fun ℓ v => (norm_symRight m _ ℓ).le) S η hη ?_
  · refine hsep.trans (mul_le_mul_of_nonneg_right ?_ hη0)
    calc ∑ τ : SymState m, ∑ ℓ, ‖symCoeff m g (symShift m τ) ℓ‖ ≤ ∑ _τ : SymState m, ∏ j, (symModulus (m j) : ℝ) :=
          Finset.sum_le_sum fun τ _ => symCoeff_mass_le m g _
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, card_symState, nsmul_eq_mul, Nat.cast_prod]
  · intro u v
    simp only [symRow, separableRow]
    push_cast
    rw [bitR_cast]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [bitR_cast]
    congr 1
    have hlook := symLookup_eq_separable m g (fun j => A j u) (fun j => B j v) (symShift m τ) (fun j => by
      have h1 := (τ j).1.isLt
      have h2 := (τ j).2.isLt
      have hA' := hA j u
      have hB' := hB j v
      simp only [symShift]
      constructor <;> omega)
    rw [← hlook]
    simp only [symLookup]
    exact Finset.prod_congr rfl fun j _ => bitR_cast _

end Sym

/-! ## Threshold tops (P3:2624-2645, 2737-2738, 2755-2756) -/

section Thr
variable {N Q : ℕ} {Gq Pr : Type} [Fintype Gq] [Fintype Pr] (prime : Pr → ℕ) [∀ pr, NeZero (prime pr)]

/-- **`reportedThr`, per row** (row:thr-reported, P3:2624-2629): `Σ_s H_{g,p,s}(u,v)·1[A_{g,p}(u)+B_{g,p}(v)+s ≡ 0 (mod p)]`. -/
noncomputable def thrRow (H : Gq → (pr : Pr) → ZMod (prime pr) → Fin N → Fin N → Bool) (A B : Gq → Pr → Fin N → ℤ)
    (g : Gq) (pr : Pr) (u v : Fin N) : ℝ :=
  ∑ s : ZMod (prime pr), bitR (H g pr s u v) * bitR (thrReported (A g pr u) (B g pr v) s)

/-- The filtered threshold-top reported observable `G·Σ_{g,p}(1/|𝒫|)R̂_{g,p}` (P3:2713-2715). -/
noncomputable def thrObservable (G : Fin N → Fin N → Bool) (H : Gq → (pr : Pr) → ZMod (prime pr) → Fin N → Fin N → Bool)
    (A B : Gq → Pr → Fin N → ℤ) (u v : Fin N) : ℝ :=
  ∑ gp : Gq × Pr, (1 / (Fintype.card Pr : ℝ)) * (bitR (G u v) * thrRow prime H A B gp.1 gp.2 u v)

/-- The THR state matrices `D_{(g,p),s} = G·H_{g,p,s}` (row:matrix). -/
noncomputable def thrStateMatrix (G : Fin N → Fin N → Bool)
    (H : Gq → (pr : Pr) → ZMod (prime pr) → Fin N → Fin N → Bool) (g : Gq) (pr : Pr) (s : ZMod (prime pr)) :
    Fin N → Fin N → ℂ :=
  stateMatrix (fun u v => bitC (G u v)) (fun s u v => bitC (H g pr s u v)) s

omit [Fintype Gq] [Fintype Pr] in
/-- One threshold row: `p` states of coefficient mass one each (P3:2639-2640) give `𝔐 = p`. -/
theorem thrRow_sample_error (hN : 0 < N) (hQ : 0 < Q) (G : Fin N → Fin N → Bool)
    (H : Gq → (pr : Pr) → ZMod (prime pr) → Fin N → Fin N → Bool) (A B : Gq → Pr → Fin N → ℤ) (g : Gq) (pr : Pr)
    (S : Fin Q → Fin N × Fin N) (η : ℝ)
    (hη : ∀ s, ‖sampleError (thrStateMatrix prime G H g pr s) S‖ / (Q * N) ≤ η) :
    |liveMean (fun u v => bitR (G u v) * thrRow prime H A B g pr u v) -
        sampleMean S (fun u v => bitR (G u v) * thrRow prime H A B g pr u v)| ≤ prime pr * η := by
  have hsep := real_sample_error hN hQ (fun u v => bitR (G u v) * thrRow prime H A B g pr u v)
    (fun u v => bitC (G u v)) (fun s u v => bitC (H g pr s u v))
    (fun (s ℓ : ZMod (prime pr)) => ((prime pr : ℂ)⁻¹ * chi (ℓ * s)))
    (fun ℓ u => chi (ℓ * (A g pr u : ZMod (prime pr)))) (fun ℓ v => chi (ℓ * (B g pr v : ZMod (prime pr))))
    (fun ℓ u => (norm_chi _).le) (fun ℓ v => (norm_chi _).le) S η hη ?_
  · refine hsep.trans (le_of_eq ?_)
    simp only [thrCoeff_mass, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · intro u v
    simp only [thrRow, separableRow]
    push_cast
    rw [bitR_cast]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [bitR_cast, bitR_cast, thrReported_separable]

/-- **`row:sampler-interface` for THR** (P3:2721-2738, 2755-2756): with every state matrix of normalized sample error at
most `η`, the sampled filtered threshold-top observable differs from its live-pair average by at most `|𝒢|·max_p p·η`
("For THR each state has mass one, there are `p` states, and the outer row mass is `|𝒢|`"). -/
theorem thr_sampler_interface (hN : 0 < N) (hQ : 0 < Q) (G : Fin N → Fin N → Bool)
    (H : Gq → (pr : Pr) → ZMod (prime pr) → Fin N → Fin N → Bool) (A B : Gq → Pr → Fin N → ℤ)
    (S : Fin Q → Fin N × Fin N) (η pmax : ℝ) (hη0 : 0 ≤ η) (hpmax0 : 0 ≤ pmax) (hpmax : ∀ pr, (prime pr : ℝ) ≤ pmax)
    (hη : ∀ g pr s, ‖sampleError (thrStateMatrix prime G H g pr s) S‖ / (Q * N) ≤ η) :
    |liveMean (thrObservable prime G H A B) - sampleMean S (thrObservable prime G H A B)| ≤
      Fintype.card Gq * pmax * η := by
  have hL := liveMean_sum (fun _ : Gq × Pr => 1 / (Fintype.card Pr : ℝ))
    (fun gp u v => bitR (G u v) * thrRow prime H A B gp.1 gp.2 u v)
  have hS := sampleMean_sum S (fun _ : Gq × Pr => 1 / (Fintype.card Pr : ℝ))
    (fun gp u v => bitR (G u v) * thrRow prime H A B gp.1 gp.2 u v)
  have hL' : liveMean (thrObservable prime G H A B) = _ := hL
  have hS' : sampleMean S (thrObservable prime G H A B) = _ := hS
  rw [hL', hS', ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hPr0 : (0 : ℝ) ≤ 1 / (Fintype.card Pr : ℝ) := by positivity
  calc ∑ gp : Gq × Pr, |1 / (Fintype.card Pr : ℝ) *
          liveMean (fun u v => bitR (G u v) * thrRow prime H A B gp.1 gp.2 u v) -
        1 / (Fintype.card Pr : ℝ) * sampleMean S (fun u v => bitR (G u v) * thrRow prime H A B gp.1 gp.2 u v)|
      ≤ ∑ gp : Gq × Pr, 1 / (Fintype.card Pr : ℝ) * (pmax * η) := by
        refine Finset.sum_le_sum fun gp _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg hPr0]
        refine mul_le_mul_of_nonneg_left ?_ hPr0
        exact (thrRow_sample_error prime hN hQ G H A B gp.1 gp.2 S η (hη gp.1 gp.2)).trans
          (mul_le_mul_of_nonneg_right (hpmax gp.2) hη0)
    _ = Fintype.card Gq * (Fintype.card Pr * (1 / (Fintype.card Pr : ℝ))) * (pmax * η) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ Fintype.card Gq * 1 * (pmax * η) := by
        have hle : (Fintype.card Pr : ℝ) * (1 / (Fintype.card Pr : ℝ)) ≤ 1 := by
          rcases eq_or_ne (Fintype.card Pr : ℝ) 0 with h | h
          · rw [h, zero_mul]; exact zero_le_one
          · rw [mul_one_div_cancel h]
        have hpe : 0 ≤ pmax * η := mul_nonneg hpmax0 hη0
        gcongr
    _ = Fintype.card Gq * pmax * η := by ring

end Thr

/-! ## Averaging over columns and final seeds (P3:2723-2728, 2757-2760) -/

/-- **The averaged interface**: if at every column `z` and final seed `e` the sampled observable errs by at most
`𝔐·η_z` (`η_z = max_{ρ,e,t}` normalized sample error at `z`) and `E_z η_z ≤ η`, then the average filtered reported
observable changes by at most `𝔐η` ("Averaging over final source seeds has total weight one [...] Averaging its
pointwise upper bound over `z` proves the result"). -/
theorem averaged_sample_error {Zc Es : Type} [Fintype Zc] [Fintype Es] [Nonempty Es] (live samp : Zc → Es → ℝ)
    (Mf : ℝ) (ηz : Zc → ℝ) (η : ℝ) (hM : 0 ≤ Mf) (hpt : ∀ z e, |live z e - samp z e| ≤ Mf * ηz z)
    (hη : uMean ηz ≤ η) :
    |uMean (fun z => uMean (fun e => live z e)) - uMean (fun z => uMean (fun e => samp z e))| ≤ Mf * η := by
  rw [← uMean_sub']
  refine (abs_uMean_le _).trans ?_
  calc uMean (fun z => |uMean (fun e => live z e) - uMean (fun e => samp z e)|)
      ≤ uMean (fun z => Mf * ηz z) := by
        refine uMean_mono fun z => ?_
        rw [← uMean_sub']
        refine (abs_uMean_le _).trans (uMean_le_const _ _ ?_ fun e => hpt z e)
        exact (abs_nonneg _).trans (hpt z (Classical.arbitrary Es))
    _ = Mf * uMean ηz := uMean_const_mul Mf ηz
    _ ≤ Mf * η := mul_le_mul_of_nonneg_left hη hM

end NearCubicWires.WireExponent3_5.Rows
