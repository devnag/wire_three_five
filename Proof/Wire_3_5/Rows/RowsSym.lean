import Proof.Wire_3_5.Rows.RowsFourier

/-! # Rows: the symmetric-top reported conjunction as a separable row (P3:2467-2539)

Realizes the symmetric-top rows (P3:2467-2539): "Circuit `j` has `m_j` bottom occurrences and an explicit lookup
`g_j:{0,…,m_j}→{0,1}` [...] Use the output alphabet `{0,…,m_j}` [...] The reported Boolean conjunction is
`R̂_e(z,u,v)=Σ_τ H_{e,τ}(z,u,v)Π_{j=1}^a g_j(A_{j,z}(u)+B_{j,z}(v)+t_j^+−t_j^−)` [...] Choose the integer `P_j=6m_j+2` [...]
The possible arguments in (row:sym-reported) lie in `[−2m_j,3m_j]`, so their residues modulo `P_j` are distinct. Define a
Boolean function `f_j` on `ℤ/P_jℤ` agreeing with the extended `g_j` on this interval and zero on unused residues [...]
Substituting `s=A_{j,z}(u)+B_{j,z}(v)+t_j^+−t_j^−` separates each summand into a coefficient, a function of `u`, and a
function of `v`. The last two functions have modulus one. Multiplying for `a` circuits yields, for each state `τ`, at most
`Π_jP_j` rank-one terms."

Main quantities: `symModulus m = 6m+2` (`P_j`), `periodicLookup` (`f_j`), the per-state coefficients `symCoeff`, the
selectors `symLeft`, `symRight`, and the reported lookup `symLookup`. Results: `periodicLookup_cast` (`f_j` agrees with
`g_j` on `[−2m_j,3m_j]`), **`symLookup_eq_separable`** (for every state in the alphabet and every one-sided scores in
range, `Π_j g_j(A_j+B_j+t_j^+−t_j^−) = Σ_ℓ c(τ,ℓ)a_ℓ(u)b_ℓ(v)`), **`symCoeff_mass_le`** (`Σ_ℓ|c(τ,ℓ)| ≤ Π_jP_j`,
F5), and the selectors' modulus one. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.Shared ZMod Finset

/-- `P_j = 6m_j + 2` (P3:2507-2509). -/
def symModulus (m : ℕ) : ℕ := 6 * m + 2

instance (m : ℕ) : NeZero (symModulus m) := ⟨by unfold symModulus; omega⟩

/-- A bit as a complex number. -/
def bitC (b : Bool) : ℂ := if b then 1 else 0

theorem norm_bitC_le (b : Bool) : ‖bitC b‖ ≤ 1 := by cases b <;> simp [bitC]

/-- The periodic lookup `f_j` on `ℤ/P_jℤ`: `g_j` at the residues of `[0,3m_j]` and of `[−2m_j,−1]`, zero elsewhere
(P3:2511-2513). -/
noncomputable def periodicLookup (m : ℕ) (g : ℤ → Bool) (r : ZMod (symModulus m)) : ℂ :=
  if r.val ≤ 3 * m then bitC (g r.val)
  else if 4 * m + 2 ≤ r.val then bitC (g ((r.val : ℤ) - symModulus m)) else 0

theorem norm_periodicLookup_le (m : ℕ) (g : ℤ → Bool) (r : ZMod (symModulus m)) : ‖periodicLookup m g r‖ ≤ 1 := by
  unfold periodicLookup; split_ifs <;> simp [norm_bitC_le]

/-- `f_j` agrees with `g_j` on the argument interval `[−2m_j, 3m_j]` (P3:2509-2512). -/
theorem periodicLookup_cast (m : ℕ) (g : ℤ → Bool) (s : ℤ) (hs1 : -(2 * (m : ℤ)) ≤ s) (hs2 : s ≤ 3 * m) :
    periodicLookup m g (s : ZMod (symModulus m)) = bitC (g s) := by
  have hP : (0 : ℤ) < symModulus m := by unfold symModulus; push_cast; omega
  have hval : ((s : ZMod (symModulus m)).val : ℤ) = s % (symModulus m : ℤ) := by
    rw [ZMod.val_intCast]
  unfold periodicLookup
  rcases le_or_gt 0 s with h0 | h0
  · have hmod : s % (symModulus m : ℤ) = s := Int.emod_eq_of_lt h0 (by unfold symModulus; push_cast; omega)
    have hv : ((s : ZMod (symModulus m)).val : ℤ) = s := by rw [hval, hmod]
    have hle : (s : ZMod (symModulus m)).val ≤ 3 * m := by omega
    rw [if_pos hle, hv]
  · have hmod : s % (symModulus m : ℤ) = s + symModulus m := by
      have h1 := Int.add_mul_emod_self_left s (symModulus m : ℤ) 1
      rw [mul_one] at h1
      rw [← h1]
      exact Int.emod_eq_of_lt (by unfold symModulus; push_cast; omega) (by omega)
    have hv : ((s : ZMod (symModulus m)).val : ℤ) = s + symModulus m := by rw [hval, hmod]
    have hPm : ((symModulus m : ℕ) : ℤ) = 6 * m + 2 := by unfold symModulus; push_cast; ring
    have hge' : (4 * m + 2 : ℤ) ≤ ((s : ZMod (symModulus m)).val : ℤ) := by rw [hv, hPm]; linarith
    have hge : 4 * m + 2 ≤ (s : ZMod (symModulus m)).val := by exact_mod_cast hge'
    have hnle : ¬ (s : ZMod (symModulus m)).val ≤ 3 * m := by omega
    rw [if_neg hnle, if_pos hge, hv]
    congr 2; ring

/-! ## The separable form of the reported conjunction -/

variable {a : ℕ}

/-- The per-state Fourier coefficient `c(τ,ℓ) = Π_j f̂_j(ℓ_j)·ω_j^{ℓ_j(t_j^+−t_j^−)}`. -/
noncomputable def symCoeff (m : Fin a → ℕ) (g : Fin a → ℤ → Bool) (τ : Fin a → ℤ)
    (ℓ : (j : Fin a) → ZMod (symModulus (m j))) : ℂ :=
  ∏ j, fourierCoeff (periodicLookup (m j) (g j)) (ℓ j) * chi (ℓ j * (τ j : ZMod (symModulus (m j))))

/-- The left selector `a_ℓ(u) = Π_j ω_j^{ℓ_jA_j(u)}` (modulus one). -/
noncomputable def symLeft (m : Fin a → ℕ) (A : Fin a → ℤ) (ℓ : (j : Fin a) → ZMod (symModulus (m j))) : ℂ :=
  ∏ j, chi (ℓ j * (A j : ZMod (symModulus (m j))))

/-- The right selector `b_ℓ(v) = Π_j ω_j^{ℓ_jB_j(v)}` (modulus one). -/
noncomputable def symRight (m : Fin a → ℕ) (B : Fin a → ℤ) (ℓ : (j : Fin a) → ZMod (symModulus (m j))) : ℂ :=
  ∏ j, chi (ℓ j * (B j : ZMod (symModulus (m j))))

theorem norm_symLeft (m : Fin a → ℕ) (A : Fin a → ℤ) (ℓ : (j : Fin a) → ZMod (symModulus (m j))) :
    ‖symLeft m A ℓ‖ = 1 := by
  unfold symLeft; rw [norm_prod]; simp [norm_chi]

theorem norm_symRight (m : Fin a → ℕ) (B : Fin a → ℤ) (ℓ : (j : Fin a) → ZMod (symModulus (m j))) :
    ‖symRight m B ℓ‖ = 1 := by
  unfold symRight; rw [norm_prod]; simp [norm_chi]

/-- The reported lookup of one state: `Π_j g_j(A_j + B_j + τ_j)` as a complex bit (P3:2489-2494). -/
def symLookup (g : Fin a → ℤ → Bool) (A B τ : Fin a → ℤ) : ℂ := ∏ j, bitC (g j (A j + B j + τ j))

/-- **The separable form** (P3:2530-2536): for arguments in `[−2m_j, 3m_j]`,
`Π_j g_j(A_j + B_j + τ_j) = Σ_ℓ c(τ,ℓ)·a_ℓ(A)·b_ℓ(B)`. -/
theorem symLookup_eq_separable (m : Fin a → ℕ) (g : Fin a → ℤ → Bool) (A B τ : Fin a → ℤ)
    (hrange : ∀ j, -(2 * (m j : ℤ)) ≤ A j + B j + τ j ∧ A j + B j + τ j ≤ 3 * m j) :
    symLookup g A B τ = ∑ ℓ : (j : Fin a) → ZMod (symModulus (m j)), symCoeff m g τ ℓ * symLeft m A ℓ * symRight m B ℓ := by
  unfold symLookup symCoeff symLeft symRight
  have hj : ∀ j, bitC (g j (A j + B j + τ j)) = ∑ lj : ZMod (symModulus (m j)),
      fourierCoeff (periodicLookup (m j) (g j)) lj * chi (lj * (τ j : ZMod (symModulus (m j)))) *
        chi (lj * (A j : ZMod (symModulus (m j)))) * chi (lj * (B j : ZMod (symModulus (m j)))) := by
    intro j
    rw [← periodicLookup_cast (m j) (g j) _ (hrange j).1 (hrange j).2,
      fourier_inversion (periodicLookup (m j) (g j))]
    refine Finset.sum_congr rfl fun lj _ => ?_
    push_cast
    rw [show lj * ((A j : ZMod (symModulus (m j))) + (B j) + (τ j)) =
      lj * (τ j : ZMod (symModulus (m j))) + lj * (A j) + lj * (B j) by ring, chi_add, chi_add]
    ring
  simp only [hj]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- **The coefficient mass** (F5): `Σ_ℓ |c(τ,ℓ)| ≤ Π_j P_j` for every state. -/
theorem symCoeff_mass_le (m : Fin a → ℕ) (g : Fin a → ℤ → Bool) (τ : Fin a → ℤ) :
    ∑ ℓ : (j : Fin a) → ZMod (symModulus (m j)), ‖symCoeff m g τ ℓ‖ ≤ ∏ j, (symModulus (m j) : ℝ) := by
  have hterm : ∀ ℓ : (j : Fin a) → ZMod (symModulus (m j)), ‖symCoeff m g τ ℓ‖ ≤ 1 := by
    intro ℓ
    unfold symCoeff
    rw [norm_prod]
    apply Finset.prod_le_one (fun j _ => norm_nonneg _)
    intro j _
    rw [norm_mul, norm_chi, mul_one]
    exact norm_fourierCoeff_le _ (norm_periodicLookup_le _ _) _
  calc ∑ ℓ : (j : Fin a) → ZMod (symModulus (m j)), ‖symCoeff m g τ ℓ‖
      ≤ ∑ _ℓ : (j : Fin a) → ZMod (symModulus (m j)), (1 : ℝ) := Finset.sum_le_sum fun ℓ _ => hterm ℓ
    _ = ∏ j, (symModulus (m j) : ℝ) := by simp [Fintype.card_pi, ZMod.card]

end NearCubicWires.WireExponent3_5.Rows
