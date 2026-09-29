import Proof.Wire_3_5.FinalPass.ThrPtPopD

/-! # S2 (THR per point), part 7: the population builder, whole (P3:2596-2606)

`popW sgn`: skip `1^p 0 1^{r₀} 0` (`skipU` twice), `m, rem := M` (`copyM`), the occurrences (`occLoop`), the missing
entries padded with `0` (`padLoop`), the three streams rewound. **`popW_spec`**: the population stream becomes
`frame (popZ sgn D as X)`, everything else as it was. Paper quantity: the digit population of digit `D`
(`thrDigitPop`, P3:2598-2599), padded to the occurrence count. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop

variable (cap : ℕ)

/-! ## Padding -/

theorem wr_z (s : PSt) (b : Bool) : WExec cap (.wr 2 b) s.w { s with z := writeTapeBit s.z s.zh b }.w 1 := by
  have h := WExec.wr (cap := cap) (2 : Fin 3) b s.w
  rwa [show s.w.st 2 = s.z from rfl, show s.w.sh 2 = s.zh from rfl, p_z] at h

theorem fwd_z (s : PSt) : WExec cap (.fwd 2) s.w { s with zh := s.zh + 1 }.w 1 := by
  have h := WExec.fwd (cap := cap) (2 : Fin 3) s.w
  rwa [show s.w.sh 2 = s.zh from rfl, p_zh] at h

/-- One padding entry: marker `1`, bit `0`. -/
def padStep : PProg := .seq (.wr 2 true) (.seq (.fwd 2) (.seq (.wr 2 false) (.seq (.fwd 2) (.seq (.inc 8) (.inc 8)))))

theorem padStep_spec (s : PSt) (W zr : List Bool) (z0 z1 : Bool) (hZ : s.z = frameP W ++ z0 :: z1 :: zr)
    (hzh : s.zh = (frameP W).length) (hc : s.hz + 2 ≤ cap) :
    WExec cap padStep s.w { s with z := frameP (W ++ [false]) ++ zr, zh := s.zh + 2, hz := s.hz + 2 }.w 16 := by
  have e1 := wr_z cap s true
  have e2 := fwd_z cap { s with z := writeTapeBit s.z s.zh true }
  have e3 := wr_z cap { { s with z := writeTapeBit s.z s.zh true } with zh := s.zh + 1 } false
  have e4 := fwd_z cap { { { s with z := writeTapeBit s.z s.zh true } with zh := s.zh + 1 } with
    z := writeTapeBit (writeTapeBit s.z s.zh true) (s.zh + 1) false }
  have e5 := inc_hz cap { { { { s with z := writeTapeBit s.z s.zh true } with zh := s.zh + 1 } with
    z := writeTapeBit (writeTapeBit s.z s.zh true) (s.zh + 1) false } with zh := s.zh + 1 + 1 } (by simp only; omega)
  have e6 := inc_hz cap { { { { { s with z := writeTapeBit s.z s.zh true } with zh := s.zh + 1 } with
    z := writeTapeBit (writeTapeBit s.z s.zh true) (s.zh + 1) false } with zh := s.zh + 1 + 1 } with
    hz := s.hz + 1 } (by simp only; omega)
  have hw1 : writeTapeBit s.z s.zh true = frameP W ++ true :: z1 :: zr := by
    rw [hZ, hzh, writeTapeBit_mid']
  have hw2 : writeTapeBit (frameP W ++ true :: z1 :: zr) (s.zh + 1) false = frameP (W ++ [false]) ++ zr := by
    have := writeTapeBit_mid' (frameP W ++ [true]) zr z1 false
    rw [List.length_append, List.length_singleton, ← hzh] at this
    rw [show frameP W ++ true :: z1 :: zr = frameP W ++ [true] ++ z1 :: zr by simp, this]
    simp [frameP]
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) (w_eq ?_)
    (by omega)
  simp only [hw1, hw2]

/-- The padding: `REM` entries `(1, 0)`. -/
def padLoop : PProg := .whr 9 (.seq (.dec 9) padStep)

theorem padLoop_spec (k : ℕ) : ∀ (s : PSt) (W zr0 : List Bool), s.rem = k → s.z = frameP W ++ zr0 ++ [false] →
    zr0.length = 2 * k → s.zh = (frameP W).length → s.hz + 2 * k ≤ cap → k ≤ cap →
    WExec cap padLoop s.w
      { s with z := frameP (W ++ List.replicate k false) ++ [false], zh := s.zh + 2 * k, hz := s.hz + 2 * k,
               rem := 0 }.w (k * 20 + 1) := by
  induction k with
  | zero =>
    intro s W zr0 hr hZ hzr _ _ _
    obtain rfl : zr0 = [] := List.eq_nil_of_length_eq_zero (by simpa using hzr)
    refine WExec.cast cap (WExec.whrF (show s.w.val 9 = 0 from hr)) (w_eq ?_) (by omega)
    obtain ⟨⟩ := s
    simp only at hr hZ ⊢
    subst hr hZ
    simp
  | succ k ih =>
    intro s W zr0 hr hZ hzr hzh hc hk
    obtain ⟨z0, z1, zr, rfl⟩ : ∃ z0 z1 zr, zr0 = z0 :: z1 :: zr := by
      match zr0, hzr with
      | z0 :: z1 :: zr, _ => exact ⟨z0, z1, zr, rfl⟩
      | [], h => simp only [List.length_nil] at h; omega
      | [_], h => simp only [List.length_cons, List.length_nil] at h; omega
    have e0 := dec_rem cap s (by omega)
    have e1 := padStep_spec cap { s with rem := s.rem - 1 } W (zr ++ [false]) z0 z1 (by simp only; rw [hZ]; simp) hzh
      (by simp only; omega)
    have e2 := ih { { s with rem := s.rem - 1 } with
        z := frameP (W ++ [false]) ++ (zr ++ [false]), zh := s.zh + 2, hz := s.hz + 2 } (W ++ [false]) zr
      (by simp only; omega) (by simp)
      (by simp at hzr; omega) (by simp only; rw [hzh, fP_length, fP_length]; simp; ring) (by simp only; omega)
      (by omega)
    refine WExec.cast cap (WExec.whrT (show s.w.val 9 ≠ 0 by show s.rem ≠ 0; omega) (WExec.seq e0 e1) e2) (w_eq ?_)
      (by rw [Nat.add_mul, Nat.one_mul]; omega)
    have hrep : W ++ [false] ++ List.replicate k false = W ++ List.replicate (k + 1) false := by
      rw [List.replicate_succ, List.append_assoc, List.singleton_append]
    simp only [hrep, PSt.mk.injEq, true_and, and_true]
    omega

/-! ## Counters -/

/-- `M := MM` into `M` and `REM` (through `T`), `MM` kept. -/
def copyM : PProg := .seq (WM.move 10 3) (.whr 3 (.seq (.dec 3) (.seq (.inc 10) (.seq (.inc 1) (.inc 9)))))

theorem copyLoop_spec (n : ℕ) : ∀ (s : PSt), s.t = n → s.mm + n ≤ cap → s.m + n ≤ cap → s.rem + n ≤ cap →
    n ≤ cap →
    WExec cap (.whr 3 (.seq (.dec 3) (.seq (.inc 10) (.seq (.inc 1) (.inc 9))))) s.w
      { s with t := 0, mm := s.mm + n, m := s.m + n, rem := s.rem + n }.w (n * 15 + 1) := by
  induction n with
  | zero =>
    intro s h0 _ _ _ _
    refine WExec.cast cap (WExec.whrF (show s.w.val 3 = 0 from h0)) (w_eq ?_) (by omega)
    obtain ⟨⟩ := s
    simp only at h0 ⊢
    subst h0
    simp
  | succ n ih =>
    intro s hn h1 h2 h3 hc
    have e1 := dec_t cap s (by omega)
    have e2 := inc_mm cap { s with t := s.t - 1 } (by simp only; omega)
    have e3 := inc_m cap { { s with t := s.t - 1 } with mm := s.mm + 1 } (by simp only; omega)
    have e4 := inc_rem cap { { { s with t := s.t - 1 } with mm := s.mm + 1 } with m := s.m + 1 } (by simp only; omega)
    have e5 := ih { { { { s with t := s.t - 1 } with mm := s.mm + 1 } with m := s.m + 1 } with rem := s.rem + 1 }
      (by simp only; omega) (by simp only; omega) (by simp only; omega) (by simp only; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show s.w.val 3 ≠ 0 by show s.t ≠ 0; omega)
      (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) e5) (w_eq ?_) (by rw [Nat.add_mul, Nat.one_mul]; omega)
    simp only [PSt.mk.injEq, true_and, and_true]
    omega

theorem copyM_spec (s : PSt) (M : ℕ) (hmm : s.mm = M) (ht : s.t = 0) (hm : s.m = 0) (hr : s.rem = 0)
    (hc : 2 * M + 2 ≤ cap) :
    WExec cap copyM s.w { s with m := M, rem := M }.w (7 * M + 1 + 1 + (M * 15 + 1)) := by
  have e1 : WExec cap (WM.move 10 3) s.w { s with mm := 0, t := M }.w (7 * M + 1) := by
    have h := wmove_spec cap (10 : Fin 11) 3 (by decide) M s.w hmm (by show s.mm ≤ cap; omega)
      (by show s.t + s.mm ≤ cap; omega)
    rw [p_mm, show s.w.val 3 = s.t from rfl, show s.w.val 10 = s.mm from rfl, p_t] at h
    refine WExec.cast cap h (w_eq ?_) le_rfl
    simp only [PSt.mk.injEq, true_and, and_true]
    omega
  have e2 := copyLoop_spec cap M { s with mm := 0, t := M } rfl (by simp only; omega) (by simp only; omega)
    (by simp only; omega) (by omega)
  refine WExec.cast cap (WExec.seq e1 e2) (w_eq ?_) le_rfl
  simp only [PSt.mk.injEq, true_and, and_true]
  omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
