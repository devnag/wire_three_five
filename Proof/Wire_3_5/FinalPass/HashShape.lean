import Proof.Wire_3_5.FinalPass.EnumCap6

/-! # The HASH printed objective's shape: term count, coefficients, factors

`filt:soft`, P3:2253-2290 (`hashTermsM`, one term per valid odometer cell `(q, e, p, λ, ι, γ)`): the printed
expression has at most `N²·n_E·|pops|·(J+1)·(2^{ℓ₀})^{2t}·2^{2t}` terms (`hashTermsM_length_le`); every term is a cell's
`(W·c, F_{q,e} :: [Z_{ι_r}]_r)` (`mem_hashTermsM`) with `|W·c| ≤ prodW·2^{2tℓ₀}` (the cleared weight at most `Π_jW_j^{2t}`,
the elimination count at most the `2^{2tℓ₀ − |p|}` completions, `hashTerm_coef`), and its factors are the HASH tape's
row `F_{q,e}` or a population gate's corner form `Z_{gi}` at star row `q` (`hashTerm_factors`).

* `hcell_length_le`, `digitsF_length`, **`hashTermsM_length_le`**, **`mem_hashTermsM`**, `mem_hcell`,
  `wOf_le`, `cntG_le`, **`hashTerm_coef`**, **`hashTerm_factors`**.

Paper quantity of the main types: the HASH printed conditional objective's terms. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.SeedFix NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimT.HashB

variable (MP : MajorantParams)

theorem hcell_length_le (G : ℕ) (F : F2Poly ℕ) (q : ℕ) (pop : Bool × List ℕ) (plen pre lam : ℕ)
    (ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0)) (γ : Fin (2 * MP.t) → Bool) :
    (hcell MP G F q pop plen pre lam ι γ).length ≤ 1 := by
  unfold hcell; split_ifs <;> simp

theorem digitsF_length (m r : ℕ) : (digitsF m r).length = m ^ r := by simp [digitsF]

/-- **The HASH objective's term count.** -/
theorem hashTermsM_length_le (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ)) (plen pre : ℕ) :
    (hashTermsM MP G N nE Fs pops plen pre).length ≤
      N ^ 2 * (nE * (pops.length * ((MP.J + 1) * ((2 ^ MP.ell0) ^ (2 * MP.t) * (2 ^ (2 * MP.t) * 1))))) := by
  unfold hashTermsM
  refine (EnumCap.flatMap_len_le _ _ _ (fun q _ => ?_)).trans (by rw [List.length_range])
  refine (EnumCap.flatMap_len_le _ _ _ (fun e _ => ?_)).trans (by rw [List.length_range])
  refine (EnumCap.flatMap_len_le _ _ _ (fun p _ => ?_)).trans (by rw [List.length_range])
  refine (EnumCap.flatMap_len_le _ _ _ (fun lam _ => ?_)).trans (by rw [List.length_range])
  refine (EnumCap.flatMap_len_le _ _ _ (fun ι _ => ?_)).trans (by rw [digitsF_length])
  refine (EnumCap.flatMap_len_le _ _ _ (fun γ _ => hcell_length_le MP _ _ _ _ _ _ _ _ _)).trans
    (by rw [digitsF_length])

/-- **Every printed term is a cell's term.** -/
theorem mem_hashTermsM (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ)) (plen pre : ℕ)
    (t : ℤ × List (F2Poly ℕ)) (ht : t ∈ hashTermsM MP G N nE Fs pops plen pre) :
    ∃ q < N ^ 2, ∃ e < nE, ∃ p < pops.length, ∃ (lam : ℕ) (ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0))
      (γ : Fin (2 * MP.t) → Bool), t ∈ hcell MP G (Fs.getD (q * nE + e) []) q (popOf pops p) plen pre lam ι γ := by
  unfold hashTermsM at ht
  simp only [List.mem_flatMap, List.mem_range] at ht
  obtain ⟨q, hq, e, he, p, hp, lam, _, ι, _, γ', _, h⟩ := ht
  exact ⟨q, hq, e, he, p, hp, lam, ι, _, h⟩

/-- A cell's term. -/
theorem mem_hcell (G : ℕ) (F : F2Poly ℕ) (q : ℕ) (pop : Bool × List ℕ) (plen pre lam : ℕ)
    (ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0)) (γ : Fin (2 * MP.t) → Bool) (t : ℤ × List (F2Poly ℕ))
    (ht : t ∈ hcell MP G F q pop plen pre lam ι γ) :
    validOf MP pop.2.length lam ι γ ∧
      t = (PrimT.HashB.wOf MP lam γ * (cntG MP (kOf MP lam) plen pre (consOf MP lam ι γ) : ℤ),
        F :: List.ofFn fun r => zPoly G q pop.1 (pop.2.getD (ι r) 0)) := by
  unfold hcell at ht
  split_ifs at ht with hc
  · exact ⟨hc.1, List.mem_singleton.mp ht⟩
  · simp at ht

theorem clearW_le (j : ℕ) (hj : j < MP.J) : clearW MP j ≤ prodW MP := by
  rw [prodW_eq MP j hj]
  have : 1 ≤ MP.W j ^ (2 * MP.t) := Nat.one_le_pow _ _ (by have := MP.W_ge j; omega)
  exact Nat.le_mul_of_pos_left _ this

/-- The cleared weight is at most `prodW` in size. -/
theorem wOf_le (lam : ℕ) (γ : Fin (2 * MP.t) → Bool) : (PrimT.HashB.wOf MP lam γ).natAbs ≤ prodW MP := by
  unfold PrimT.HashB.wOf
  split_ifs with h
  · rw [Int.natAbs_mul]
    have hs : (sgnG γ).natAbs = 1 := by unfold sgnG; simp [Int.natAbs_pow]
    rw [hs, Nat.mul_one, Int.natAbs_natCast]
    exact clearW_le MP lam h
  · rw [Int.natAbs_natCast]

/-- The elimination count is at most the `2^{2tℓ₀}` completions. -/
theorem cntG_le (lam plen pre : ℕ) (ι : Fin (2 * MP.t) → Fin (2 ^ MP.ell0)) (γ : Fin (2 * MP.t) → Bool)
    (hplen : plen ≤ 2 * MP.t * MP.ell0) :
    cntG MP (kOf MP lam) plen pre (consOf MP lam ι γ) ≤ 2 ^ (2 * MP.t * MP.ell0) := by
  have hk : kOf MP lam ≤ MP.ell0 := by
    have := MP.J_lt_ell0
    unfold kOf; split_ifs <;> omega
  have hcons : ∀ c ∈ consOf MP lam ι γ, c.1 < 2 ^ MP.ell0 ∧ c.2 < 2 ^ kOf MP lam := by
    intro c hc
    unfold consOf at hc
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc
    refine ⟨(ι r).isLt, ?_⟩
    show (if lam < MP.J ∧ γ r = true then 2 ^ lam else 0) < 2 ^ (if lam < MP.J then lam + 1 else MP.J)
    by_cases h1 : lam < MP.J
    · rw [if_pos h1]
      split_ifs
      · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      · exact Nat.one_le_two_pow
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
      exact Nat.one_le_two_pow
  have e := cntG_eq MP (kOf MP lam) plen pre (consOf MP lam ι γ) hk hplen hcons
  have h1 : (∑ r ∈ Finset.range (2 ^ (2 * MP.t * MP.ell0 - plen)),
      (if ∀ c ∈ consOf MP lam ι γ, JoinElimination.proj (kOf MP lam)
        (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) (compl plen pre r) c.1) = c.2 then (1 : ℤ) else 0)) ≤
      ∑ _r ∈ Finset.range (2 ^ (2 * MP.t * MP.ell0 - plen)), (1 : ℤ) :=
    Finset.sum_le_sum fun r _ => by split_ifs <;> norm_num
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
  have h2 : ((cntG MP (kOf MP lam) plen pre (consOf MP lam ι γ) : ℕ) : ℤ) ≤ ((2 ^ (2 * MP.t * MP.ell0 - plen) : ℕ) : ℤ) := by
    rw [e]; push_cast; exact h1
  have h3 := Nat.cast_le.mp h2
  exact h3.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))

/-- **Every printed term's coefficient is at most `prodW·2^{2tℓ₀}`.** -/
theorem hashTerm_coef (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ)) (plen pre : ℕ)
    (hplen : plen ≤ 2 * MP.t * MP.ell0) :
    ∀ t ∈ hashTermsM MP G N nE Fs pops plen pre, t.1.natAbs ≤ prodW MP * 2 ^ (2 * MP.t * MP.ell0) := by
  intro t ht
  obtain ⟨q, _, e, _, p, _, lam, ι, γ, h⟩ := mem_hashTermsM MP G N nE Fs pops plen pre t ht
  obtain ⟨_, rfl⟩ := mem_hcell MP G _ q _ plen pre lam ι γ t h
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul (wOf_le MP lam γ) (cntG_le MP lam plen pre ι γ hplen)

/-- **Every printed term's factors**: the HASH tape's row `F_{q,e}` or a population gate's corner form at row `q`. -/
theorem hashTerm_factors (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ)) (plen pre : ℕ)
    (t : ℤ × List (F2Poly ℕ)) (ht : t ∈ hashTermsM MP G N nE Fs pops plen pre) :
    ∃ q < N ^ 2, ∃ e < nE, ∃ p < pops.length, ∀ f ∈ t.2,
      f = Fs.getD (q * nE + e) [] ∨ ∃ gi ∈ (popOf pops p).2, f = zPoly G q (popOf pops p).1 gi := by
  obtain ⟨q, hq, e, he, p, hp, lam, ι, γ, h⟩ := mem_hashTermsM MP G N nE Fs pops plen pre t ht
  obtain ⟨hv, rfl⟩ := mem_hcell MP G _ q _ plen pre lam ι γ t h
  refine ⟨q, hq, e, he, p, hp, fun f hf => ?_⟩
  rcases List.mem_cons.mp hf with rfl | hf
  · left; rfl
  · right
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hf
    refine ⟨_, ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ (hv.1 r)]
    exact List.getElem_mem _

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
