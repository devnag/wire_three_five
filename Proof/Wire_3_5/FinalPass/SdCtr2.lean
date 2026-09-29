import Proof.Wire_3_5.FinalPass.SdCtr1

/-! # S4 (the seeds phase), part 11: a loop over all the values of a binary counter (P3:1206-1216)

The loops over the table positions (`row < 2^{dRow}`, `col < 2^{dR}`) share one shape: `cntW row Body` runs `Body`
at the counter's value `x`, then the all-ones test sets the flag `[x ≠ 2^d − 1]`, and a set flag increments the counter
(`cntInc`); the loop runs while the flag is set. **`cntW_spec`**: for a loop state `J` insensitive to the counter's
word and flag, a body adding `g x` to `J`'s accumulator and keeping the counter (`CntAt`), the loop from `x` (flag
set) adds `Σ_{x ≤ y < 2^d} g y` and ends at the counter `2^d − 1`, flag clear (the body may use the bound
`a + Σ_{x ≤ y < 2^d} g y ≤ Bd` on its accumulator).

Paper quantity of the main type: a sum over the table positions `Σ_{y < 2^d} g y`, run by a binary counter. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass

section Lay
variable {nw nn nsc nrs : ℕ}

/-- **The counter at `x` with flag `f`**: the word `frame (binary d x)`, head `0`, position and spare registers `0`. -/
structure CntAt (row : Bool) (d x f : ℕ) (ω : BS nw nn nsc nrs) : Prop where
  st : ω.st (cT row) = frame (binary d x)
  sh : ω.sh (cT row) = 0
  c : ω.val (cC row) = 0
  f : ω.val (cF row) = f
  k : ω.val (cK row) = 0

theorem cntAt_setF (row : Bool) (d x f f' : ℕ) (ω : BS nw nn nsc nrs) (h : CntAt row d x f ω) :
    CntAt row d x f' (ω.setv (cF row) f') :=
  ⟨h.st, h.sh, by rw [wsetv_val_ne _ _ (cCF row)]; exact h.c, by simp,
    by rw [wsetv_val_ne _ _ (cFK row).symm]; exact h.k⟩

/-- **The loop over the counter's values.** -/
def cntW (row : Bool) (Body : BP nw nn nsc nrs) : BP nw nn nsc nrs :=
  .whr (cF row) (.seq (.dec (cF row)) (.seq Body (.seq (cntMax row) (.ifr (cF row) (cntInc row) .skip))))

/-- One value's cost around the body. -/
def cntCost (d T cb : ℕ) : ℕ := 1 + 1 + (cb + 1 + (d * 20 + 1 + 1 + (5 * (2 * d) + 1) + 1 + (incCost T + 1))) + 2

theorem cntW_spec (cap : ℕ) (row : Bool) (d T cb Bd : ℕ) (Body : BP nw nn nsc nrs)
    (J : ℕ → BS nw nn nsc nrs → Prop)
    (g : ℕ → ℕ) (hJs : ∀ a (ω : BS nw nn nsc nrs) s, J a ω → J a (ω.sets (cT row) s))
    (hJv : ∀ a (ω : BS nw nn nsc nrs) v, J a ω → J a (ω.setv (cF row) v))
    (hB : ∀ x a (ω : BS nw nn nsc nrs), x < 2 ^ d → a + ∑ y ∈ Finset.Ico x (2 ^ d), g y ≤ Bd → J a ω →
      CntAt row d x 0 ω → ∃ ω', WExec cap Body ω ω' cb ∧ J (a + g x) ω' ∧ CntAt row d x 0 ω')
    (hdT : d ≤ T) (hc1 : 2 * T + 2 < cap) (hc2 : 2 * d + 1 ≤ cap) :
    ∀ (m x a : ℕ) (ω : BS nw nn nsc nrs), x + m = 2 ^ d → 1 ≤ m → a + ∑ y ∈ Finset.Ico x (2 ^ d), g y ≤ Bd →
      J a ω → CntAt row d x 1 ω →
      ∃ ω', WExec cap (cntW row Body) ω ω' (m * cntCost d T cb + 1) ∧
        J (a + ∑ y ∈ Finset.Ico x (2 ^ d), g y) ω' ∧ CntAt row d (2 ^ d - 1) 0 ω'
  | 0, _, _, _, _, h1, _, _, _ => absurd h1 (by omega)
  | m + 1, x, a, ω, hx, _, hBd, hJ, hC => by
    have hxd : x < 2 ^ d := by omega
    -- the flag cleared
    have e0 := WExec.dec (cap := cap) (cF row) ω (by rw [hC.f]; omega)
    rw [hC.f, Nat.sub_self] at e0
    have hJ0 := hJv a ω 0 hJ
    have hC0 := cntAt_setF row d x 1 0 ω hC
    -- the body
    obtain ⟨ω1, e1, hJ1, hC1⟩ := hB x a _ hxd hBd hJ0 hC0
    -- the test
    have e2 := cnt_max cap row d x hxd ω1 hC1.st hC1.sh hC1.c hC1.f hc2
    have hJ2 := hJv _ ω1 (if x + 1 = 2 ^ d then 0 else 1) hJ1
    have hC2 := cntAt_setF row d x 0 (if x + 1 = 2 ^ d then 0 else 1) ω1 hC1
    have hsum : ∑ y ∈ Finset.Ico x (2 ^ d), g y = g x + ∑ y ∈ Finset.Ico (x + 1) (2 ^ d), g y :=
      Finset.sum_eq_sum_Ico_succ_bot hxd g
    by_cases hmax : x + 1 = 2 ^ d
    · -- the last value
      have hm : m = 0 := by omega
      subst hm
      have hf : (ω1.setv (cF row) (if x + 1 = 2 ^ d then 0 else 1)).val (cF row) = 0 := by simp [hmax]
      refine ⟨_, WExec.mono (WExec.whrT (by rw [hC.f]; omega) (WExec.seq e0 (WExec.seq e1 (WExec.seq e2
        (WExec.ifrF hf (WExec.skip _))))) (WExec.whrF hf)) (by unfold cntCost; omega), ?_, ?_⟩
      · rw [hsum, show Finset.Ico (x + 1) (2 ^ d) = ∅ by rw [hmax]; simp, Finset.sum_empty, Nat.add_zero]
        exact hJ2
      · rw [show 2 ^ d - 1 = x by omega]
        convert hC2 using 1
        simp [hmax]
    · -- the next value
      have hf : (ω1.setv (cF row) (if x + 1 = 2 ^ d then 0 else 1)).val (cF row) = 1 := by simp [hmax]
      have e3 := cnt_inc cap row d x T (by omega) (by
          have : 2 ^ d ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) hdT
          omega) (ω1.setv (cF row) (if x + 1 = 2 ^ d then 0 else 1)) hC2.st hC2.sh hC2.c hc1
      obtain ⟨ω', e', hJ', hC'⟩ := cntW_spec cap row d T cb Bd Body J g hJs hJv hB hdT hc1 hc2 m (x + 1) (a + g x)
        ((ω1.setv (cF row) (if x + 1 = 2 ^ d then 0 else 1)).sets (cT row) (frame (binary d (x + 1))))
        (by omega) (by omega) (by rw [hsum] at hBd; omega) (hJs _ _ (frame (binary d (x + 1))) hJ2)
        ⟨by simp, by simp only [WState.sets_sh]; exact hC2.sh, by simp only [WState.sets_val]; exact hC2.c,
          by simp only [WState.sets_val]; exact hf, by simp only [WState.sets_val]; exact hC2.k⟩
      refine ⟨ω', WExec.mono (WExec.whrT (by rw [hC.f]; omega) (WExec.seq e0 (WExec.seq e1 (WExec.seq e2
        (WExec.ifrT (by rw [hf]; omega) e3)))) e') (by unfold cntCost; rw [Nat.add_mul, Nat.one_mul]; omega), ?_, hC'⟩
      rw [hsum, ← Nat.add_assoc]
      exact hJ'

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.Sd
