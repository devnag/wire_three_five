import Proof.Wire_3_5.Foundations.S0
import Proof.Foundations.ThresholdCompiler

/-! # `alg:stack` (P3:1771-1796) and `alg:binlift` (P3:1800-1828) on separated equations

Realizes `alg:stack`: "Let `E_1,…,E_t` be integer separated equations as above. Suppose `V ≥ 0` is an integer with
`|E_j(z)| ≤ V` for every `j, z`, and set `H = 2V+2`. Then `∏_j 1[E_j(z)=0] = 1[Σ_j H^{j−1}E_j(z) = 0]`. The stacked
equation is separated" (P3:1774-1782); and `alg:binlift`: "Suppose the Boolean polynomial `p` is the exclusive-or of
`M` Boolean monomials `G_1,…,G_M` [...] `BinLift_Q(p) = Σ_{ℓ=1}^Q (−2)^{ℓ−1} Σ_{|J|=ℓ} ∏_{j∈J} G_j`. It equals `p`
modulo `2^Q` on every input. It has at most `Q·max(1,M)^Q` occurrences" (P3:1803-1812).

The stacking induction needs only `H > V` (`H = 2V + 2` is one choice). The binomial lift is the base's numeric
`ThresholdCompiler.binLift` (`≡ t mod 2`, `binLiftModEqParity`) read through the count of the true monomials.

Main declarations: **`stackEquations H Es`** (the ref) with **`stack_holds_iff`** and `stack_value_abs_le`;
`sum_sublistsLen_all` (`Σ_{|J|=ℓ} ∏_{j∈J} G_j = C(#true, ℓ)`), **`binLiftValue`** (the lifted value of a list of
monomials) with **`binLiftValue_eq`** (`= binLift Q t`), **`binLiftValue_modEq`** (`≡ p mod 2^Q`), and the occurrence count
`binLift_count_le` (`Σ_{ℓ≤Q} C(M,ℓ) ≤ Q·max(1,M)^Q`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

/-! ## Stacking -/

/-- **The stacked equation** `Σ_j H^{j−1}E_j` (P3:1779-1782): left and right halves summed separately with the same
powers of `H`; the empty stack is `0 = 0`. -/
def stackEquations {ZL ZR : Type} (H : ℤ) : List (SeparatedEquation ZL ZR) → SeparatedEquation ZL ZR
  | [] => ⟨fun _ => 0, fun _ => 0⟩
  | E :: Es => ⟨fun zl => E.left zl + H * (stackEquations H Es).left zl,
      fun zr => E.right zr + H * (stackEquations H Es).right zr⟩

/-- The value of a separated equation. -/
def eqValue {ZL ZR : Type} (E : SeparatedEquation ZL ZR) (zl : ZL) (zr : ZR) : ℤ := E.left zl + E.right zr

theorem holds_iff {ZL ZR : Type} (E : SeparatedEquation ZL ZR) (zl : ZL) (zr : ZR) :
    E.holds zl zr = true ↔ eqValue E zl zr = 0 := by
  simp [SeparatedEquation.holds, eqValue]

theorem stack_value {ZL ZR : Type} (H : ℤ) (E : SeparatedEquation ZL ZR) (Es : List (SeparatedEquation ZL ZR))
    (zl : ZL) (zr : ZR) :
    eqValue (stackEquations H (E :: Es)) zl zr = eqValue E zl zr + H * eqValue (stackEquations H Es) zl zr := by
  simp only [stackEquations, eqValue]; ring

/-- **`alg:stack`** (P3:1774-1782): if every stacked equation has `|E(z)| ≤ V` and `H > V`, the stacked equation holds
exactly when all of them hold. -/
theorem stack_holds_iff {ZL ZR : Type} (H V : ℤ) (hHV : V < H) (Es : List (SeparatedEquation ZL ZR))
    (zl : ZL) (zr : ZR) (hV : ∀ E ∈ Es, |eqValue E zl zr| ≤ V) :
    (stackEquations H Es).holds zl zr = true ↔ ∀ E ∈ Es, E.holds zl zr = true := by
  induction Es with
  | nil => simp [stackEquations, SeparatedEquation.holds]
  | cons E Es ih =>
    rw [holds_iff, stack_value]
    have ih' := ih (fun E' hE' => hV E' (List.mem_cons_of_mem _ hE'))
    rw [holds_iff] at ih'
    have hE := hV E List.mem_cons_self
    simp only [List.mem_cons, forall_eq_or_imp]
    rw [holds_iff, ← ih']
    constructor
    · intro h
      set w := eqValue (stackEquations H Es) zl zr
      by_cases hw : w = 0
      · refine ⟨by rw [hw] at h; linarith, hw⟩
      · exfalso
        have h1 : eqValue E zl zr = -(H * w) := by linarith
        have hV0 : 0 ≤ V := le_trans (abs_nonneg _) hE
        have hH0 : 0 < H := lt_of_le_of_lt hV0 hHV
        have h2 : H ≤ |H * w| := by
          rw [abs_mul, abs_of_pos hH0]
          have : 1 ≤ |w| := Int.one_le_abs hw
          nlinarith
        rw [h1, abs_neg] at hE
        linarith
    · rintro ⟨h1, h2⟩; rw [h1, h2]; ring

/-! ## The binomial lift -/

/-- The occurrence count: `Σ_{ℓ=1}^Q C(M,ℓ) ≤ Q·max(1,M)^Q` (P3:1811-1812, 1825-1826). -/
theorem binLift_count_le (Q M : ℕ) :
    ∑ j ∈ Finset.range Q, M.choose (j + 1) ≤ Q * max 1 M ^ Q := by
  calc ∑ j ∈ Finset.range Q, M.choose (j + 1) ≤ ∑ _j ∈ Finset.range Q, max 1 M ^ Q := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j + 1 ≤ Q := Finset.mem_range.mp hj
        calc M.choose (j + 1) ≤ M ^ (j + 1) := Nat.choose_le_pow M (j + 1)
          _ ≤ max 1 M ^ (j + 1) := Nat.pow_le_pow_left (le_max_right 1 M) _
          _ ≤ max 1 M ^ Q := Nat.pow_le_pow_right (by omega) hj'
    _ = Q * max 1 M ^ Q := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end NearCubicWires.WireExponent3_5.Compiler
