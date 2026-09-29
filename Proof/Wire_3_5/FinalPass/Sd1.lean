import Proof.Wire_3_5.FinalPass.ThrPtRS15

/-! # S4 (the seeds phase), part 1: the binary accumulator (P3:3044-3048)

The numerator `Σ_{c,e,l} mask·Σ R̂` is kept as `frame (binary W x)` (least significant bit first). **`binary_inc`**:
`x + 1 < 2^W` ⇒ `binary W x = 1^t 0 rest`, `binary W (x+1) = 0^t 1 rest`. On the one-stream layout (`USt`):
**`incB_spec`** (the word becomes `frame (binary W (x+1))`, head and position counter back at `0`; its cost depends
on a bound `T` with `x + 1 < 2^T`, not on the width `W`: `ones_le`) and
**`addLoop_spec`** (register `2`'s value `v` added: `frame (binary W (x+v))`, the register consumed). Paper quantity:
the printed numerator `fpNum` in `W`-bit binary (NumDenOut). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

theorem binary_inc : ∀ (W x : ℕ), x + 1 < 2 ^ W → ∃ t rest,
    binary W x = List.replicate t true ++ false :: rest ∧ binary W (x + 1) = List.replicate t false ++ true :: rest
  | 0, x, h => absurd h (by simp)
  | W + 1, x, h => by
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · refine ⟨0, binary W (x / 2), ?_, ?_⟩
      · simp [SignedSortKey.binary, hx]
      · have h1 : (x + 1) % 2 = 1 := by omega
        have h2 : (x + 1) / 2 = x / 2 := by omega
        simp [SignedSortKey.binary, h1, h2]
    · have hlt : x / 2 + 1 < 2 ^ W := by rw [pow_succ] at h; omega
      obtain ⟨t, rest, e1, e2⟩ := binary_inc W (x / 2) hlt
      refine ⟨t + 1, rest, ?_, ?_⟩
      · simp [SignedSortKey.binary, hx, e1, List.replicate_succ]
      · have h1 : (x + 1) % 2 = 0 := by omega
        have h2 : (x + 1) / 2 = x / 2 + 1 := by omega
        simp [SignedSortKey.binary, h1, h2, e2, List.replicate_succ]

/-- `t` trailing ones: `2^t ≤ x + 1` (so an increment's carry is shorter than any `T` with `x + 1 < 2^T`). -/
theorem ones_le : ∀ (t W x : ℕ) (rest : List Bool), binary W x = List.replicate t true ++ false :: rest →
    2 ^ t ≤ x + 1
  | 0, _, _, _, _ => by simp
  | t + 1, 0, x, rest, h => by simp [SignedSortKey.binary] at h
  | t + 1, W + 1, x, rest, h => by
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · simp [SignedSortKey.binary, hx, List.replicate_succ] at h
    · have h' : binary W (x / 2) = List.replicate t true ++ false :: rest := by
        simpa [SignedSortKey.binary, hx, List.replicate_succ] using h
      have := ones_le t W (x / 2) rest h'
      rw [pow_succ]
      omega

theorem set_rep (i : ℕ) (b c : Bool) (X : List Bool) :
    (List.replicate i c ++ b :: X).set i c = List.replicate (i + 1) c ++ X := by
  rw [List.set_append_right _ _ (by simp), List.length_replicate, Nat.sub_self, List.set_cons_zero,
    List.replicate_succ', List.append_assoc, List.singleton_append]

theorem getD_rep (i : ℕ) (b c : Bool) (X : List Bool) : (List.replicate i c ++ b :: X).getD i false = b := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

variable (cap : ℕ)

/-- The carry loop: `1`s become `0`s until the first `0`. -/
def incLoop : UProg := .whs 0 (.seq (.wr 0 false) (.seq (WM.fwdC 0 0) (WM.fwdC 0 0)))

theorem incLoop_spec (rest R : List Bool) : ∀ (m i : ℕ) (u : USt),
    u.s = frameP (List.replicate i false ++ (List.replicate m true ++ false :: rest)) ++ R →
    u.h = 2 * i + 1 → u.c = 2 * i + 1 → 2 * (i + m) + 1 < cap →
    WExec cap incLoop u.w { u with
      s := frameP (List.replicate (i + m) false ++ false :: rest) ++ R, h := 2 * (i + m) + 1,
      c := 2 * (i + m) + 1 }.w (m * 15 + 1)
  | 0, i, u, hs, hh, hc, _ => by
    have hb : wbit u.w 0 = false := by
      show readTapeBit u.s u.h = false
      rw [hs, hh, readTapeBit_frameP _ _ _ (by simp)]
      simp
    refine WExec.cast cap (WExec.whsF hb) (uw_eq (USt.ext' ?_ ?_ ?_ rfl rfl rfl)) (by omega)
    · show u.s = _; rw [hs]; simp
    · show u.h = 2 * (i + 0) + 1; omega
    · show u.c = 2 * (i + 0) + 1; omega
  | m + 1, i, u, hs, hh, hc, hcap => by
    have hL : i < (List.replicate i false ++ (List.replicate (m + 1) true ++ false :: rest)).length := by simp
    have hb : wbit u.w 0 = true := by
      show readTapeBit u.s u.h = true
      rw [hs, hh, readTapeBit_frameP _ _ _ hL, List.replicate_succ, List.cons_append]
      exact getD_rep i true false _
    have e1 := u_wr cap u false
    have hw : writeTapeBit u.s u.h false =
        frameP (List.replicate (i + 1) false ++ (List.replicate m true ++ false :: rest)) ++ R := by
      rw [hs, hh, frameP_set _ _ _ _ hL, List.replicate_succ, List.cons_append, set_rep]
    rw [hw] at e1
    have e2 := u_fwdC cap { u with
      s := frameP (List.replicate (i + 1) false ++ (List.replicate m true ++ false :: rest)) ++ R }
      (by show u.c < cap; omega)
    have e3 := u_fwdC cap { { u with
      s := frameP (List.replicate (i + 1) false ++ (List.replicate m true ++ false :: rest)) ++ R } with
      h := u.h + 1, c := u.c + 1 } (by show u.c + 1 < cap; omega)
    have ih := incLoop_spec rest R m (i + 1) { { { u with
      s := frameP (List.replicate (i + 1) false ++ (List.replicate m true ++ false :: rest)) ++ R } with
      h := u.h + 1, c := u.c + 1 } with h := u.h + 1 + 1, c := u.c + 1 + 1 } rfl (by show u.h + 1 + 1 = _; omega)
      (by show u.c + 1 + 1 = _; omega) (by omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih) (uw_eq (USt.ext' ?_ ?_ ?_ rfl rfl rfl))
      (by omega)
    · show frameP (List.replicate (i + 1 + m) false ++ false :: rest) ++ R =
        frameP (List.replicate (i + (m + 1)) false ++ false :: rest) ++ R
      rw [show i + 1 + m = i + (m + 1) by omega]
    · show 2 * (i + 1 + m) + 1 = 2 * (i + (m + 1)) + 1; omega
    · show 2 * (i + 1 + m) + 1 = 2 * (i + (m + 1)) + 1; omega

/-- **One binary increment**, the head rewound. -/
def incB : UProg := .seq (WM.fwdC 0 0) (.seq incLoop (.seq (.wr 0 true) (WM.rewind 0 0)))

/-- `incB`'s step bound when the value stays below `2^T` (the carry is shorter than `T`; the width `W` never enters). -/
def incCost (T : ℕ) : ℕ := 5 + 1 + ((T * 15 + 1) + 1 + (1 + 1 + (5 * (2 * T + 1) + 1)))

theorem incB_spec (W T x : ℕ) (hx : x + 1 < 2 ^ W) (hT : x + 1 < 2 ^ T) (R : List Bool) (u : USt)
    (hs : u.s = frameP (binary W x) ++ false :: R) (hh : u.h = 0) (hc : u.c = 0) (hcap : 2 * T + 2 < cap) :
    WExec cap incB u.w { u with s := frameP (binary W (x + 1)) ++ false :: R }.w (incCost T) := by
  obtain ⟨t, rest, e1, e2⟩ := binary_inc W x hx
  have htT : t < T := by
    have h1 := ones_le t W x rest e1
    by_contra hn
    have h2 : 2 ^ T ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlen : t + 1 + rest.length = W := by
    have := congrArg List.length e1
    simp [Corner.binary_length'] at this
    omega
  have f1 := u_fwdC cap u (by omega)
  have f2 := incLoop_spec cap rest (false :: R) t 0 { u with h := u.h + 1, c := u.c + 1 }
    (by show u.s = _; rw [hs, e1]; simp) (by show u.h + 1 = _; omega) (by show u.c + 1 = _; omega) (by omega)
  obtain ⟨U2, hU2⟩ : ∃ v : USt, v = { { u with h := u.h + 1, c := u.c + 1 } with
      s := frameP (List.replicate (0 + t) false ++ false :: rest) ++ false :: R, h := 2 * (0 + t) + 1,
      c := 2 * (0 + t) + 1 } := ⟨_, rfl⟩
  rw [← hU2] at f2
  have hw : writeTapeBit U2.s U2.h true = frameP (binary W (x + 1)) ++ false :: R := by
    rw [hU2]
    show writeTapeBit (frameP (List.replicate (0 + t) false ++ false :: rest) ++ false :: R) (2 * (0 + t) + 1) true = _
    rw [frameP_set _ _ _ _ (by simp), Nat.zero_add, e2, List.set_append_right _ _ (by simp), List.length_replicate,
      Nat.sub_self, List.set_cons_zero]
  have f3 := u_wr cap U2 true
  rw [hw] at f3
  have f4 := u_rew cap { U2 with s := frameP (binary W (x + 1)) ++ false :: R }
    (by rw [hU2]; show 2 * (0 + t) + 1 ≤ cap; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq f1 (WExec.seq f2 (WExec.seq f3 f4))) (uw_eq ?_) le_rfl) ?_
  · subst hU2
    exact USt.ext' rfl (by show 2 * (0 + t) + 1 - (2 * (0 + t) + 1) = u.h; omega) (by show 0 = u.c; omega) rfl rfl rfl
  · have hc4 : ({ U2 with s := frameP (binary W (x + 1)) ++ false :: R } : USt).c = 2 * (0 + t) + 1 := by
      rw [hU2]
    rw [hc4]
    unfold incCost
    omega

/-- **`v` added**: register `2` counts the increments. -/
def addLoop : UProg := .whr 2 (.seq (.dec 2) incB)

theorem addLoop_spec (W T : ℕ) (R : List Bool) (hcap : 2 * T + 2 < cap) : ∀ (v x : ℕ) (u : USt),
    u.s = frameP (binary W x) ++ false :: R → u.h = 0 → u.c = 0 → u.k = v → x + v < 2 ^ W → x + v < 2 ^ T →
    v ≤ cap →
    WExec cap addLoop u.w { u with s := frameP (binary W (x + v)) ++ false :: R, k := 0 }.w
      (v * (incCost T + 4) + 1)
  | 0, x, u, hs, _, _, hk, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (show u.w.val 2 = 0 from hk)) (uw_eq (USt.ext' ?_ rfl rfl rfl ?_ rfl))
      (by omega)
    · show u.s = _; rw [hs, Nat.add_zero]
    · show u.k = 0; exact hk
  | v + 1, x, u, hs, hh, hc, hk, hx, hxT, hv => by
    have e1 := u_decK cap u (by omega)
    have e2 := incB_spec cap W T x (by omega) (by omega) R { u with k := u.k - 1 } hs hh hc hcap
    have ih := addLoop_spec W T R hcap v (x + 1)
      { { u with k := u.k - 1 } with s := frameP (binary W (x + 1)) ++ false :: R }
      rfl hh hc (by show u.k - 1 = v; omega) (by omega) (by omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show u.w.val 2 ≠ 0 by show u.k ≠ 0; omega) (WExec.seq e1 e2) ih)
      (uw_eq (USt.ext' ?_ rfl rfl rfl rfl rfl)) (by rw [Nat.add_mul, Nat.one_mul]; omega)
    · show frameP (binary W (x + 1 + v)) ++ false :: R = frameP (binary W (x + (v + 1))) ++ false :: R
      rw [show x + 1 + v = x + (v + 1) by omega]

end NearCubicWires.WireExponent3_5.FinalPass.Sd
