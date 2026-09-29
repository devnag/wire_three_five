import Proof.Wire_3_5.FinalPass.S5TPre2

/-! # S5-THR, part 3: the powers and the whole count program (P3:3170-3181)

* `chainW`, `chainSt`, **`chainW_spec`**: `D` products `xs (k+1) := xs k × T`, so `xs j = sent (b^{j+1})`;
* `preW`, `preSt`, **`preW_spec`**: from `frame u` on `I`: `T = sent b`, `xs j = sent (b^{j+1})` (`j ≤ D`),
  `C = 1^{b^{D+1}}`, `b = |u| + 1`, every head back at `0`, nothing else touched.

Paper quantity of the main type: the front's register capacity (its unary count `(|fpIn|+1)^{D+1}`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

/-! ## The powers -/

/-- `D` products: `xs (k+1) := xs k × T`. -/
def chainW (xs : ℕ → Fin (ns + 1)) (T : Fin (ns + 1)) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (chainW xs T k) (mulW (xs k) T (xs (k + 1)))

/-- The state after `k` products. -/
def chainSt (σ : WState ns nr) (xs : ℕ → Fin (ns + 1)) (b : ℕ) : ℕ → WState ns nr
  | 0 => σ
  | k + 1 => (chainSt σ xs b k).sets (xs (k + 1)) (sent (b ^ (k + 2)))

/-- The products' cost. -/
def chainCost (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => chainCost b k + 1 + mulCost (b ^ (k + 1)) b

section Chain
variable (xs : ℕ → Fin (ns + 1)) (T : Fin (ns + 1))

theorem chainSt_sh (σ : WState ns nr) (b : ℕ) : ∀ k, (chainSt σ xs b k).sh = σ.sh
  | 0 => rfl
  | k + 1 => by simp [chainSt, chainSt_sh σ b k]

theorem chainSt_cell (σ : WState ns nr) (b : ℕ) : ∀ k, (chainSt σ xs b k).cell = σ.cell
  | 0 => rfl
  | k + 1 => by simp [chainSt, chainSt_cell σ b k]

theorem chainSt_st_ne (σ : WState ns nr) (b : ℕ) (i : Fin (ns + 1)) : ∀ k, (∀ j, 1 ≤ j → j ≤ k → xs j ≠ i) →
    (chainSt σ xs b k).st i = σ.st i
  | 0, _ => rfl
  | k + 1, h => by
    simp only [chainSt, WState.sets_st]
    rw [Function.update_of_ne (Ne.symm (h (k + 1) (by omega) le_rfl)),
      chainSt_st_ne σ b i k (fun j h1 h2 => h j h1 (by omega))]

theorem chainSt_st_self (K : ℕ) (hxs : ∀ i j, i ≤ K → j ≤ K → xs i = xs j → i = j) (σ : WState ns nr) (b : ℕ) :
    ∀ k j, k ≤ K → 1 ≤ j → j ≤ k → (chainSt σ xs b k).st (xs j) = sent (b ^ (j + 1))
  | 0, j, _, h1, h2 => by omega
  | k + 1, j, hk, h1, h2 => by
    simp only [chainSt, WState.sets_st]
    by_cases hj : j = k + 1
    · subst hj; simp
    · rw [Function.update_of_ne (fun e => hj (hxs _ _ (by omega) hk e)),
        chainSt_st_self K hxs σ b k j (by omega) h1 (by omega)]

theorem chainW_spec (K : ℕ) (hxs : ∀ i j, i ≤ K → j ≤ K → xs i = xs j → i = j) (hT : ∀ j, j ≤ K → xs j ≠ T)
    (b : ℕ) (σ : WState ns nr) (h0 : σ.st (xs 0) = sent b) (hTs : σ.st T = sent b) (hTh : σ.sh T = 0)
    (hsh : ∀ j, j ≤ K → σ.sh (xs j) = 0) :
    ∀ k, k ≤ K → (∀ j, 1 ≤ j → j ≤ k → σ.st (xs j) = []) →
      WExec cap (chainW xs T k) σ (chainSt σ xs b k) (chainCost b k)
  | 0, _, _ => WExec.skip σ
  | k + 1, hK, hb => by
    have ih := chainW_spec K hxs hT b σ h0 hTs hTh hsh k (by omega) (fun j h1 h2 => hb j h1 (by omega))
    have hX : (chainSt σ xs b k).st (xs k) = sent (b ^ (k + 1)) := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [chainSt]; simpa using h0
      · exact chainSt_st_self xs K hxs σ b k k (by omega) hk le_rfl
    have hTk : (chainSt σ xs b k).st T = sent b := by
      rw [chainSt_st_ne xs σ b T k (fun j _ h2 => hT j (by omega)), hTs]
    have hY : (chainSt σ xs b k).st (xs (k + 1)) = [] := by
      rw [chainSt_st_ne xs σ b (xs (k + 1)) k (fun j _ h2 e => by have := hxs _ _ (by omega) hK e; omega)]
      exact hb (k + 1) (by omega) le_rfl
    have e := mulW_spec cap (xs k) T (xs (k + 1)) (hT k (by omega))
      (fun e => by have := hxs _ _ (by omega) hK e; omega)
      (Ne.symm (hT (k + 1) hK)) (b ^ (k + 1)) b (chainSt σ xs b k) hX (by rw [chainSt_sh, hsh k (by omega)])
      hTk (by rw [chainSt_sh, hTh]) hY (by rw [chainSt_sh, hsh (k + 1) hK])
    rw [← pow_succ] at e
    exact WExec.seq ih e

end Chain

/-! ## The count program -/

end NearCubicWires.WireExponent3_5.FinalPass.S5T
