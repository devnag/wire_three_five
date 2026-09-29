import Proof.Wire_3_5.FinalPass.ThrPtPopC

/-! # S2 (THR per point), part 6: the population builder (P3:2596-2606)

`popW sgn`: skip `1^p 0 1^{r₀} 0` on the row word; `m := M`, `rem := M`; for each of the `M` occurrences the step
of part 5 (`occLoop`); then the `rem` missing entries padded with `0` (`padLoop`); the three streams rewound.
**`popW_spec`**: from the row word `rowWord`'s prefix and coefficients, the framed corner word `frameP X` (`|X| = 4M`)
and a population stream of `2M + 1` cells ending in `false`, the population stream becomes
`frame (popZ sgn D as X)`: the selected bits `selB` padded with `0` to length `M`; everything else as it was.
Paper quantity: the digit population `thrDigitPop` of digit `D` (P3:2598-2599), padded to the occurrence count. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop

/-- **The padded population**: the selected bits, then `0`s up to `M` entries. -/
def popZ (sgn : Bool) (d : ℕ) (as : List ℕ) (X : List Bool) : List Bool :=
  selB sgn d as X ++ List.replicate (as.length - (selB sgn d as X).length) false

theorem popZ_length (sgn : Bool) (d : ℕ) (as : List ℕ) (X : List Bool) : (popZ sgn d as X).length = as.length := by
  have := selB_length_le sgn d as X
  simp [popZ]; omega

variable (cap : ℕ)

/-! ## The occurrences -/

/-- All occurrences. -/
def occLoop (sgn : Bool) : PProg := .whr 1 (.seq (.dec 1) (occStep sgn))

theorem occLoop_spec (sgn : Bool) (D A0 : ℕ) (restR restX : List Bool) (hA : 2 * A0 + 2 ≤ cap)
    (hD : 2 * D + 2 ≤ cap) : ∀ (asS : List ℕ) (XS : List Bool) (asP : List ℕ) (XP zr0 : List Bool) (s : PSt),
    XP.length = 4 * asP.length → XS.length = 4 * asS.length → (∀ a ∈ asS, a ≤ A0) →
    s.rw.drop s.rwh = asS.flatMap ListEval.unary ++ restR →
    s.x = frameP (XP ++ XS) ++ restX → s.xh = 2 * XP.length → s.hx = s.xh →
    s.z = frameP (selB sgn D asP XP) ++ zr0 ++ [false] → zr0.length = 2 * s.rem →
    s.zh = 2 * (selB sgn D asP XP).length → s.hz = s.zh → asS.length ≤ s.rem →
    s.m = asS.length → s.d = D → s.a = 0 → s.t = 0 → s.e = 0 → s.pb = 0 →
    s.hr + (asS.map (· + 1)).sum + A0 + 1 ≤ cap → s.xh + 8 * asS.length ≤ cap → s.zh + 2 * asS.length ≤ cap →
    s.rem ≤ cap →
    ∃ zr1 : List Bool, zr1.length = 2 * (s.rem + (selB sgn D asP XP).length -
        (selB sgn D (asP ++ asS) (XP ++ XS)).length) ∧
      WExec cap (occLoop sgn) s.w
        { s with rwh := s.rwh + (asS.map (· + 1)).sum, hr := s.hr + (asS.map (· + 1)).sum,
                 xh := s.xh + 8 * asS.length, hx := s.xh + 8 * asS.length,
                 z := frameP (selB sgn D (asP ++ asS) (XP ++ XS)) ++ zr1 ++ [false],
                 zh := 2 * (selB sgn D (asP ++ asS) (XP ++ XS)).length,
                 hz := 2 * (selB sgn D (asP ++ asS) (XP ++ XS)).length,
                 rem := s.rem + (selB sgn D asP XP).length - (selB sgn D (asP ++ asS) (XP ++ XS)).length,
                 m := 0 }.w (asS.length * (occCost A0 D + 4) + 1) := by
  intro asS
  induction asS with
  | nil =>
    intro XS asP XP zr0 s hXP hXS _ _ _ hxh hhx hz hzr hzh hhz _ hm _ _ _ _ _ _ _ _ _
    obtain rfl : XS = [] := List.eq_nil_of_length_eq_zero (by simpa using hXS)
    refine ⟨zr0, by simp [hzr], WExec.cast cap (WExec.whrF (show s.w.val 1 = 0 from hm)) (w_eq ?_) (by simp)⟩
    obtain ⟨⟩ := s
    simp at hxh hhx hz hzh hhz hm ⊢
    subst hz hhx hhz hm
    pst_rec
  | cons a asS ih =>
    intro XS asP XP zr0 s hXP hXS hA0 hrw hX hxh hhx hz hzr hzh hhz hrem hm hd ha ht he hp hc1 hc2 hc3 hc4
    obtain ⟨b1, b2, b3, b4, XS', rfl⟩ : ∃ b1 b2 b3 b4 XS', XS = b1 :: b2 :: b3 :: b4 :: XS' := by
      match XS, hXS with
      | b1 :: b2 :: b3 :: b4 :: XS', _ => exact ⟨b1, b2, b3, b4, XS', rfl⟩
      | [], h => simp only [List.length_nil, List.length_cons] at h; omega
      | [_], h => simp only [List.length_nil, List.length_cons] at h; omega
      | [_, _], h => simp only [List.length_nil, List.length_cons] at h; omega
      | [_, _, _], h => simp only [List.length_nil, List.length_cons] at h; omega
    have hXS' : XS'.length = 4 * asS.length := by simp at hXS; omega
    have hsum : ((a :: asS).map (· + 1)).sum = a + 1 + (asS.map (· + 1)).sum := by simp
    rw [hsum] at hc1
    have ha0 : a ≤ A0 := hA0 a (by simp)
    have hA0' : ∀ a' ∈ asS, a' ≤ A0 := fun a' h => hA0 a' (by simp [h])
    have hrw' : s.rw.drop s.rwh = ListEval.unary a ++ (asS.flatMap ListEval.unary ++ restR) := by
      rw [hrw]; simp
    have hXsplit : s.x = frameP XP ++ frameP [b1, b2, b3, b4] ++ (frameP XS' ++ restX) := by
      rw [hX]; simp [frameP]
    have hlen : asS.length + 1 ≤ s.rem := by simpa using hrem
    have hml : s.m = asS.length + 1 := by simpa using hm
    have hdrop : (s.rw.drop (s.rwh + a + 1)) = asS.flatMap ListEval.unary ++ restR := by
      rw [show s.rwh + a + 1 = s.rwh + (a + 1) by omega, ← List.drop_drop, hrw']
      exact List.drop_left' (by simp [ListEval.unary])
    have hXeq : XP ++ b1 :: b2 :: b3 :: b4 :: XS' = XP ++ [b1, b2, b3, b4] ++ XS' := by simp
    have hAeq : asP ++ a :: asS = asP ++ [a] ++ asS := by simp
    have e0 := dec_m cap s (by omega)
    by_cases hbit : a / 2 ^ D % 2 = 1
    · -- selected
      obtain ⟨z0, z1, zr, rfl⟩ : ∃ z0 z1 zr, zr0 = z0 :: z1 :: zr := by
        match zr0, hzr with
        | z0 :: z1 :: zr, _ => exact ⟨z0, z1, zr, rfl⟩
        | [], h => simp at h; omega
        | [_], h => simp at h; omega
      have e1 := occStep_sel cap sgn D a A0 { s with m := s.m - 1 } (asS.flatMap ListEval.unary ++ restR) XP
        [b1, b2, b3, b4] (frameP XS' ++ restX) (selB sgn D asP XP) (zr ++ [false]) z0 z1 hrw' ha0 hbit rfl hXsplit hxh
        (by simp only; rw [hz]; simp) hzh hd ha ht he hp (by simp only; omega) (by simp only; omega)
        hA hD (by simp only; omega) (by simp only; omega) (by simp only; omega)
      have hsel : selB sgn D (asP ++ [a]) (XP ++ [b1, b2, b3, b4]) = selB sgn D asP XP ++ [popG sgn [b1, b2, b3, b4]] :=
        by rw [selB_snoc sgn D asP XP a [b1, b2, b3, b4] hXP rfl, if_pos hbit]
      have hzr' : zr.length = 2 * (s.rem - 1) := by simp at hzr; omega
      obtain ⟨zr1, hzr1, e2⟩ := ih XS' (asP ++ [a]) (XP ++ [b1, b2, b3, b4]) zr
        { { s with m := s.m - 1 } with
          rwh := s.rwh + a + 1, hr := s.hr + a + 1,
          z := frameP (selB sgn D asP XP ++ [popG sgn [b1, b2, b3, b4]]) ++ (zr ++ [false]), xh := s.xh + 8,
          zh := 2 * (selB sgn D asP XP).length + 2, hx := s.hx + 8, hz := s.hz + 2, rem := s.rem - 1 }
        (by simp; omega) hXS' hA0' (by simp only; exact hdrop) (by simp only; rw [hX, hXeq])
        (by simp only; rw [hxh]; simp; ring) (by simp only; omega) (by simp only; rw [hsel]; simp)
        (by simp only; exact hzr') (by simp only; rw [hsel]; simp; ring) (by simp only; omega)
        (by simp only; omega) (by simp only; omega) hd ha ht he hp (by simp only; omega)
        (by simp only; omega) (by simp only; omega) (by simp only; omega)
      have hl1 := selB_length_le sgn D (asP ++ [a] ++ asS) (XP ++ [b1, b2, b3, b4] ++ XS')
      refine ⟨zr1, ?_, WExec.cast cap (WExec.whrT (show s.w.val 1 ≠ 0 by show s.m ≠ 0; omega)
        (WExec.seq e0 e1) e2) (w_eq ?_) ?_⟩
      · rw [hzr1, hAeq, hXeq, hsel]
        simp only [List.length_append, List.length_singleton]
        omega
      · rw [hAeq, hXeq]
        simp only [hsel, List.length_append, List.length_singleton, PSt.mk.injEq, true_and, and_true]
        omega
      · simp only [List.length_cons]
        rw [Nat.add_mul]
        omega
    · -- skipped
      have hbit0 : a / 2 ^ D % 2 = 0 := by omega
      have e1 := occStep_skip cap sgn D a A0 { s with m := s.m - 1 } (asS.flatMap ListEval.unary ++ restR) hrw' ha0
        hbit0 hd ha ht he hp (by simp only; omega) hA hD (by simp only; omega)
      have hsel : selB sgn D (asP ++ [a]) (XP ++ [b1, b2, b3, b4]) = selB sgn D asP XP := by
        rw [selB_snoc sgn D asP XP a [b1, b2, b3, b4] hXP rfl, if_neg hbit, List.append_nil]
      obtain ⟨zr1, hzr1, e2⟩ := ih XS' (asP ++ [a]) (XP ++ [b1, b2, b3, b4]) zr0
        { { s with m := s.m - 1 } with rwh := s.rwh + a + 1, hr := s.hr + a + 1, xh := s.xh + 8, hx := s.hx + 8 }
        (by simp; omega) hXS' hA0' (by simp only; exact hdrop) (by simp only; rw [hX, hXeq])
        (by simp only; rw [hxh]; simp; ring) (by simp only; omega) (by simp only; rw [hsel]; exact hz)
        (by simp only; exact hzr) (by simp only; rw [hsel]; exact hzh) (by simp only; omega)
        (by simp only; omega) (by simp only; omega) hd ha ht he hp (by simp only; omega)
        (by simp only; omega) (by simp only; omega) (by simp only; omega)
      refine ⟨zr1, ?_, WExec.cast cap (WExec.whrT (show s.w.val 1 ≠ 0 by show s.m ≠ 0; omega)
        (WExec.seq e0 e1) e2) (w_eq ?_) ?_⟩
      · rw [hzr1, hAeq, hXeq, hsel]
      · rw [hAeq, hXeq]
        simp only [hsel, PSt.mk.injEq, true_and, and_true]
        omega
      · simp only [List.length_cons]
        rw [Nat.add_mul]
        omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
