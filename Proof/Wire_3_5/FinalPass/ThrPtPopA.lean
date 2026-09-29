import Proof.Wire_3_5.FinalPass.Pop

/-! # S2 (THR per point), part 3: the population builder's layout and the digit bit (P3:2596-2606)

The digit population of digit `d` of row `(g, p)` at a point (`thrDigitPop`, with `b₀ = 2`) is the list of the
population bits `Z_i^±` of the occurrences `i` whose reduced coefficient `a_i` has digit `d` equal to `1`
(`digitOf = a_i / 2^d mod 2`). The builder reads `a_i` in unary from the row's word (RowW) and the corners of occurrence
`i` from the corner word (stage 2), in step. This part: the layout (`PSt`, `WM 2 11`: streams `0` the row word, `1`
the framed corner word, `2` the population; registers `0` the digit `d`, `1` the occurrences left, `2` the
coefficient `a`, `3` a temporary, `4` the digit bit, `5` the halvings left, `6`/`7`/`8` the head counters, `9` the
padding left, `10` the occurrence count `M`), and the digit bit: **`halfQ_spec`** (`a ↦ ⌊a/2⌋`), **`parQ_spec`**
(`a mod 2`), **`bitD_spec`** (the bit register holds `a / 2^d mod 2`, `a` consumed, `d` kept). Paper quantity:
the digit `v_{i,d}` of `a_i` in base `2` (P3:2596-2599). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The population builder's programs. -/
abbrev PProg := WM 2 11

/-- The population builder's phase record. -/
structure PSt where
  rw : List Bool
  x : List Bool
  z : List Bool
  rwh : ℕ
  xh : ℕ
  zh : ℕ
  d : ℕ
  m : ℕ
  a : ℕ
  t : ℕ
  pb : ℕ
  e : ℕ
  hr : ℕ
  hx : ℕ
  hz : ℕ
  rem : ℕ
  mm : ℕ
  cell : Bool

/-- The word state of a phase record. -/
def PSt.w (s : PSt) : WState 2 11 :=
  ⟨![s.rwh, s.xh, s.zh], ![s.rw, s.x, s.z], ![s.d, s.m, s.a, s.t, s.pb, s.e, s.hr, s.hx, s.hz, s.rem, s.mm], s.cell⟩

/-- Close an equality of word states against phase records. -/
syntax "pst_eq" : tactic
macro_rules
  | `(tactic| pst_eq) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | (funext i; fin_cases i <;> first | rfl | (simp [PSt.w]; done) | (simp [PSt.w] <;> omega))
        | rfl
        | (simp [PSt.w]; done)))

section Upd
variable (s : PSt) (v : ℕ) (l : List Bool)

theorem p_d : s.w.setv 0 v = { s with d := v }.w := by pst_eq
theorem p_m : s.w.setv 1 v = { s with m := v }.w := by pst_eq
theorem p_a : s.w.setv 2 v = { s with a := v }.w := by pst_eq
theorem p_t : s.w.setv 3 v = { s with t := v }.w := by pst_eq
theorem p_pb : s.w.setv 4 v = { s with pb := v }.w := by pst_eq
theorem p_e : s.w.setv 5 v = { s with e := v }.w := by pst_eq
theorem p_hr : s.w.setv 6 v = { s with hr := v }.w := by pst_eq
theorem p_hx : s.w.setv 7 v = { s with hx := v }.w := by pst_eq
theorem p_hz : s.w.setv 8 v = { s with hz := v }.w := by pst_eq
theorem p_rem : s.w.setv 9 v = { s with rem := v }.w := by pst_eq
theorem p_mm : s.w.setv 10 v = { s with mm := v }.w := by pst_eq
theorem p_rwh : s.w.seth 0 v = { s with rwh := v }.w := by pst_eq
theorem p_xh : s.w.seth 1 v = { s with xh := v }.w := by pst_eq
theorem p_zh : s.w.seth 2 v = { s with zh := v }.w := by pst_eq
theorem p_z : s.w.sets 2 l = { s with z := l }.w := by pst_eq

end Upd

variable (cap : ℕ)

/-! ## Steps to declared records -/

theorem w_eq {s s' : PSt} (h : s = s') : s.w = s'.w := congrArg PSt.w h

/-! ## Register steps -/

theorem inc_d (s : PSt) (hc : s.d < cap) : WExec cap (.inc 0) s.w { s with d := s.d + 1 }.w 3 := by
  have h := WExec.inc (cap := cap) 0 s.w hc
  rwa [show s.w.val 0 = s.d from rfl, p_d] at h

theorem dec_m (s : PSt) (hc : s.m ≤ cap) : WExec cap (.dec 1) s.w { s with m := s.m - 1 }.w 1 := by
  have h := WExec.dec (cap := cap) 1 s.w hc
  rwa [show s.w.val 1 = s.m from rfl, p_m] at h

theorem inc_m (s : PSt) (hc : s.m < cap) : WExec cap (.inc 1) s.w { s with m := s.m + 1 }.w 3 := by
  have h := WExec.inc (cap := cap) 1 s.w hc
  rwa [show s.w.val 1 = s.m from rfl, p_m] at h

theorem dec_a (s : PSt) (hc : s.a ≤ cap) : WExec cap (.dec 2) s.w { s with a := s.a - 1 }.w 1 := by
  have h := WExec.dec (cap := cap) 2 s.w hc
  rwa [show s.w.val 2 = s.a from rfl, p_a] at h

theorem dec_t (s : PSt) (hc : s.t ≤ cap) : WExec cap (.dec 3) s.w { s with t := s.t - 1 }.w 1 := by
  have h := WExec.dec (cap := cap) 3 s.w hc
  rwa [show s.w.val 3 = s.t from rfl, p_t] at h

theorem inc_t (s : PSt) (hc : s.t < cap) : WExec cap (.inc 3) s.w { s with t := s.t + 1 }.w 3 := by
  have h := WExec.inc (cap := cap) 3 s.w hc
  rwa [show s.w.val 3 = s.t from rfl, p_t] at h

theorem dec_pb (s : PSt) (hc : s.pb ≤ cap) : WExec cap (.dec 4) s.w { s with pb := s.pb - 1 }.w 1 := by
  have h := WExec.dec (cap := cap) 4 s.w hc
  rwa [show s.w.val 4 = s.pb from rfl, p_pb] at h

theorem inc_pb (s : PSt) (hc : s.pb < cap) : WExec cap (.inc 4) s.w { s with pb := s.pb + 1 }.w 3 := by
  have h := WExec.inc (cap := cap) 4 s.w hc
  rwa [show s.w.val 4 = s.pb from rfl, p_pb] at h

theorem dec_e (s : PSt) (hc : s.e ≤ cap) : WExec cap (.dec 5) s.w { s with e := s.e - 1 }.w 1 := by
  have h := WExec.dec (cap := cap) 5 s.w hc
  rwa [show s.w.val 5 = s.e from rfl, p_e] at h

theorem inc_e (s : PSt) (hc : s.e < cap) : WExec cap (.inc 5) s.w { s with e := s.e + 1 }.w 3 := by
  have h := WExec.inc (cap := cap) 5 s.w hc
  rwa [show s.w.val 5 = s.e from rfl, p_e] at h

theorem inc_hx (s : PSt) (hc : s.hx < cap) : WExec cap (.inc 7) s.w { s with hx := s.hx + 1 }.w 3 := by
  have h := WExec.inc (cap := cap) 7 s.w hc
  rwa [show s.w.val 7 = s.hx from rfl, p_hx] at h

theorem inc_hz (s : PSt) (hc : s.hz < cap) : WExec cap (.inc 8) s.w { s with hz := s.hz + 1 }.w 3 := by
  have h := WExec.inc (cap := cap) 8 s.w hc
  rwa [show s.w.val 8 = s.hz from rfl, p_hz] at h

theorem dec_rem (s : PSt) (hc : s.rem ≤ cap) : WExec cap (.dec 9) s.w { s with rem := s.rem - 1 }.w 1 := by
  have h := WExec.dec (cap := cap) 9 s.w hc
  rwa [show s.w.val 9 = s.rem from rfl, p_rem] at h

theorem inc_rem (s : PSt) (hc : s.rem < cap) : WExec cap (.inc 9) s.w { s with rem := s.rem + 1 }.w 3 := by
  have h := WExec.inc (cap := cap) 9 s.w hc
  rwa [show s.w.val 9 = s.rem from rfl, p_rem] at h

theorem inc_mm (s : PSt) (hc : s.mm < cap) : WExec cap (.inc 10) s.w { s with mm := s.mm + 1 }.w 3 := by
  have h := WExec.inc (cap := cap) 10 s.w hc
  rwa [show s.w.val 10 = s.mm from rfl, p_mm] at h

/-! ## Halving and parity -/

/-- Close a record equality field by field. -/
syntax "pst_rec" : tactic
macro_rules
  | `(tactic| pst_rec) => `(tactic| all_goals ((try simp only [PSt.mk.injEq, true_and, and_true]) <;> (try omega)))

/-- `T += ⌊A/2⌋`, `A := 0`. -/
def halfQ : PProg := .whr 2 (.seq (.dec 2) (.ifr 2 (.seq (.dec 2) (.inc 3)) .skip))

theorem halfQ_body1 (s : PSt) (h1 : s.a = 1) (hc : 1 ≤ cap) :
    WExec cap (.seq (.dec 2) (.ifr 2 (.seq (.dec 2) (.inc 3)) .skip)) s.w { s with a := 0 }.w 3 := by
  have e1 := dec_a cap s (by omega)
  have e2 := WExec.ifrF (P := .seq (.dec 2) (.inc 3)) (show ({ s with a := s.a - 1 } : PSt).w.val 2 = 0 by
    show s.a - 1 = 0; omega) (WExec.skip (cap := cap) _)
  exact WExec.cast cap (WExec.seq e1 e2) (w_eq (by obtain ⟨⟩ := s; simp only at h1; pst_rec)) (by omega)

theorem halfQ_body2 (s : PSt) (n : ℕ) (h2 : s.a = n + 2) (ht : s.t < cap) (hc : n + 2 ≤ cap) :
    WExec cap (.seq (.dec 2) (.ifr 2 (.seq (.dec 2) (.inc 3)) .skip)) s.w { s with a := n, t := s.t + 1 }.w 8 := by
  have e1 := dec_a cap s (by omega)
  have e2 := dec_a cap { s with a := s.a - 1 } (by simp only; omega)
  have e3 := inc_t cap { { s with a := s.a - 1 } with a := s.a - 1 - 1 } (by simp only; omega)
  have e4 := WExec.ifrT (Q := .skip) (show ({ s with a := s.a - 1 } : PSt).w.val 2 ≠ 0 by
    show s.a - 1 ≠ 0; omega) (WExec.seq e2 e3)
  exact WExec.cast cap (WExec.seq e1 e4) (w_eq (by obtain ⟨⟩ := s; simp only at h2 ⊢; pst_rec)) (by omega)

theorem halfQ_spec : ∀ (n : ℕ) (s : PSt), s.a = n → s.t + n ≤ cap → n ≤ cap →
    WExec cap halfQ s.w { s with a := 0, t := s.t + n / 2 }.w (5 * n + 1)
  | 0, s, h0, _, _ => by
    refine WExec.cast cap (WExec.whrF (show s.w.val 2 = 0 from h0)) (w_eq ?_) (by omega)
    obtain ⟨⟩ := s; simp only at h0 ⊢; pst_rec
  | 1, s, h1, _, hc => by
    have e1 := halfQ_body1 cap s h1 (by omega)
    have e3 := WExec.whrF (cap := cap) (P := .seq (.dec 2) (.ifr 2 (.seq (.dec 2) (.inc 3)) .skip))
      (show ({ s with a := 0 } : PSt).w.val 2 = 0 from rfl)
    exact WExec.cast cap (WExec.whrT (show s.w.val 2 ≠ 0 by show s.a ≠ 0; omega) e1 e3)
      (w_eq (by obtain ⟨⟩ := s; simp only at h1 ⊢; pst_rec)) (by omega)
  | n + 2, s, h2, ht, hc => by
    have e1 := halfQ_body2 cap s n h2 (by omega) hc
    have ih := halfQ_spec n { s with a := n, t := s.t + 1 } rfl (by simp only; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show s.w.val 2 ≠ 0 by show s.a ≠ 0; omega) e1 ih) (w_eq ?_) (by omega)
    obtain ⟨⟩ := s
    simp only at h2 ⊢
    have : (n + 2) / 2 = n / 2 + 1 := by omega
    rw [this]
    pst_rec

/-- `P += A mod 2`, `A := 0`. -/
def parQ : PProg := .whr 2 (.seq (.dec 2) (.ifr 2 (.dec 2) (.inc 4)))

theorem parQ_body1 (s : PSt) (h1 : s.a = 1) (hp : s.pb < cap) (hc : 1 ≤ cap) :
    WExec cap (.seq (.dec 2) (.ifr 2 (.dec 2) (.inc 4))) s.w { s with a := 0, pb := s.pb + 1 }.w 6 := by
  have e1 := dec_a cap s (by omega)
  have e2 := inc_pb cap { s with a := s.a - 1 } (by simp only; omega)
  have e3 := WExec.ifrF (P := .dec 2) (show ({ s with a := s.a - 1 } : PSt).w.val 2 = 0 by
    show s.a - 1 = 0; omega) e2
  exact WExec.cast cap (WExec.seq e1 e3) (w_eq (by obtain ⟨⟩ := s; simp only at h1 ⊢; pst_rec)) (by omega)

theorem parQ_body2 (s : PSt) (n : ℕ) (h2 : s.a = n + 2) (hc : n + 2 ≤ cap) :
    WExec cap (.seq (.dec 2) (.ifr 2 (.dec 2) (.inc 4))) s.w { s with a := n }.w 4 := by
  have e1 := dec_a cap s (by omega)
  have e2 := dec_a cap { s with a := s.a - 1 } (by simp only; omega)
  have e3 := WExec.ifrT (Q := .inc 4) (show ({ s with a := s.a - 1 } : PSt).w.val 2 ≠ 0 by
    show s.a - 1 ≠ 0; omega) e2
  exact WExec.cast cap (WExec.seq e1 e3) (w_eq (by obtain ⟨⟩ := s; simp only at h2 ⊢; pst_rec)) (by omega)

theorem parQ_spec : ∀ (n : ℕ) (s : PSt), s.a = n → s.pb + 1 ≤ cap → n ≤ cap →
    WExec cap parQ s.w { s with a := 0, pb := s.pb + n % 2 }.w (9 * n + 1)
  | 0, s, h0, _, _ => by
    refine WExec.cast cap (WExec.whrF (show s.w.val 2 = 0 from h0)) (w_eq ?_) (by omega)
    obtain ⟨⟩ := s; simp only at h0 ⊢; pst_rec
  | 1, s, h1, hp, hc => by
    have e1 := parQ_body1 cap s h1 (by omega) (by omega)
    have e4 := WExec.whrF (cap := cap) (P := .seq (.dec 2) (.ifr 2 (.dec 2) (.inc 4)))
      (show ({ s with a := 0, pb := s.pb + 1 } : PSt).w.val 2 = 0 from rfl)
    exact WExec.cast cap (WExec.whrT (show s.w.val 2 ≠ 0 by show s.a ≠ 0; omega) e1 e4)
      (w_eq (by obtain ⟨⟩ := s; simp only at h1 ⊢)) (by omega)
  | n + 2, s, h2, hp, hc => by
    have e1 := parQ_body2 cap s n h2 hc
    have ih := parQ_spec n { s with a := n } rfl hp (by omega)
    refine WExec.cast cap (WExec.whrT (show s.w.val 2 ≠ 0 by show s.a ≠ 0; omega) e1 ih) (w_eq ?_) (by omega)
    obtain ⟨⟩ := s
    simp only at h2 ⊢
    have : (n + 2) % 2 = n % 2 := by omega
    rw [this]

/-! ## The digit bit -/

/-- `D += T`, `E += T`, `T := 0` (the digit index restored and copied). -/
def restDE : PProg := .whr 3 (.seq (.dec 3) (.seq (.inc 0) (.inc 5)))

theorem restDE_step (s : PSt) (n : ℕ) (hn : s.t = n + 1) (hd : s.d < cap) (he : s.e < cap) (hc : n + 1 ≤ cap) :
    WExec cap (.seq (.dec 3) (.seq (.inc 0) (.inc 5))) s.w { s with t := n, d := s.d + 1, e := s.e + 1 }.w 9 := by
  have e1 := dec_t cap s (by omega)
  have e2 := inc_d cap { s with t := s.t - 1 } (by simp only; omega)
  have e3 := inc_e cap { { s with t := s.t - 1 } with d := s.d + 1 } (by simp only; omega)
  exact WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) (w_eq (by obtain ⟨⟩ := s; simp only at hn ⊢; pst_rec))
    (by omega)

theorem restDE_spec (n : ℕ) : ∀ (s : PSt), s.t = n → s.d + n ≤ cap → s.e + n ≤ cap → n ≤ cap →
    WExec cap restDE s.w { s with t := 0, d := s.d + n, e := s.e + n }.w (11 * n + 1) := by
  induction n with
  | zero =>
    intro s h0 _ _ _
    refine WExec.cast cap (WExec.whrF (show s.w.val 3 = 0 from h0)) (w_eq ?_) (by omega)
    obtain ⟨⟩ := s; simp only at h0 ⊢; pst_rec
  | succ n ih =>
    intro s hn hd he hc
    have b := restDE_step cap s n hn (by omega) (by omega) hc
    have r := ih { s with t := n, d := s.d + 1, e := s.e + 1 } rfl (by simp only; omega) (by simp only; omega)
      (by omega)
    refine WExec.cast cap (WExec.whrT (show s.w.val 3 ≠ 0 by show s.t ≠ 0; omega) b r) (w_eq ?_) (by omega)
    obtain ⟨⟩ := s; simp only at hn ⊢; pst_rec

/-- `A += T`, `T := 0`. -/
def moveTA : PProg := WM.move 3 2

theorem moveTA_spec (s : PSt) (hc : s.t ≤ cap) (hc2 : s.a + s.t ≤ cap) :
    WExec cap moveTA s.w { s with t := 0, a := s.a + s.t }.w (7 * s.t + 1) := by
  have h := wmove_spec cap (3 : Fin 11) 2 (by decide) s.t s.w rfl hc hc2
  rwa [p_t, show s.w.val 2 = s.a from rfl, show s.w.val 3 = s.t from rfl, p_a] at h

/-- One halving: `E` counted down, `A := ⌊A/2⌋` (through `T`). -/
def halfStep : PProg := .seq (.dec 5) (.seq halfQ moveTA)

theorem halfStep_spec (A B : ℕ) (s : PSt) (j : ℕ) (he : s.e = j + 1) (ht : s.t = 0) (ha : s.a = B) (hB : B ≤ A)
    (hA : 2 * A + 2 ≤ cap) (hj : j + 1 ≤ cap) :
    WExec cap halfStep s.w { s with e := j, a := B / 2 }.w (12 * A + 5) := by
  have e1 := dec_e cap s (by omega)
  have e2 := halfQ_spec cap B { s with e := s.e - 1 } ha (by simp only; omega) (by omega)
  have hB2 := Nat.div_le_self B 2
  have e3 := moveTA_spec cap { { s with e := s.e - 1 } with a := 0, t := s.t + B / 2 } (by simp only; omega)
    (by simp only; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) (w_eq ?_) ?_
  · obtain ⟨⟩ := s; simp only at he ht ⊢; subst ht; pst_rec
  · simp only [ht]; omega

/-- The halvings: `A := ⌊A/2^E⌋`, `E := 0`. -/
def halves : PProg := .whr 5 halfStep

theorem halves_spec (A : ℕ) (hA : 2 * A + 2 ≤ cap) (j : ℕ) : ∀ (B : ℕ) (s : PSt), s.e = j → s.t = 0 → s.a = B →
    B ≤ A → j ≤ cap →
    WExec cap halves s.w { s with e := 0, a := B / 2 ^ j }.w (j * (12 * A + 7) + 1) := by
  induction j with
  | zero =>
    intro B s he _ ha _ _
    refine WExec.cast cap (WExec.whrF (show s.w.val 5 = 0 from he)) (w_eq ?_) (by omega)
    obtain ⟨⟩ := s; simp only at he ha ⊢; subst ha; simp only [pow_zero, Nat.div_one]; pst_rec
  | succ j ih =>
    intro B s he ht ha hB hj
    have b := halfStep_spec cap A B s j he ht ha hB hA hj
    have hB2 := Nat.div_le_self B 2
    have r := ih (B / 2) { s with e := j, a := B / 2 } rfl (by simp only; exact ht) rfl (by omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show s.w.val 5 ≠ 0 by show s.e ≠ 0; omega) b r) (w_eq ?_) ?_
    · have hq : B / 2 / 2 ^ j = B / 2 ^ (j + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ']
      obtain ⟨⟩ := s; simp only at he ⊢; rw [hq]
    · rw [Nat.add_mul, Nat.one_mul]; omega

/-- **The digit bit**: `P := ⌊A/2^D⌋ mod 2`, `A := 0`, `D` kept. -/
def bitD : PProg := .seq (WM.move 0 3) (.seq restDE (.seq halves parQ))

/-- `bitD`'s step bound. -/
def bitDCost (A D : ℕ) : ℕ := 7 * D + 1 + 1 + (11 * D + 1 + 1 + (D * (12 * A + 7) + 1 + 1 + (9 * A + 1)))

theorem bitD_spec (A D : ℕ) (s : PSt) (ha : s.a = A) (hd : s.d = D) (ht : s.t = 0) (he : s.e = 0) (hp : s.pb = 0)
    (hA : 2 * A + 2 ≤ cap) (hD : 2 * D + 2 ≤ cap) :
    WExec cap bitD s.w { s with a := 0, pb := A / 2 ^ D % 2 }.w (bitDCost A D) := by
  have e1 : WExec cap (WM.move 0 3) s.w { s with d := 0, t := D }.w (7 * D + 1) := by
    have h := wmove_spec cap (0 : Fin 11) 3 (by decide) D s.w hd (by show s.d ≤ cap; omega)
      (by show s.t + s.d ≤ cap; omega)
    rw [p_d, show s.w.val 3 = s.t from rfl, show s.w.val 0 = s.d from rfl, p_t] at h
    refine WExec.cast cap h (w_eq ?_) le_rfl
    obtain ⟨⟩ := s; simp only at hd ht ⊢; pst_rec
  have e2 := restDE_spec cap D { s with d := 0, t := D } rfl (by simp only; omega) (by simp only; omega) (by omega)
  have e3 := halves_spec cap A hA D A { s with d := 0 + D, t := 0, e := s.e + D } (by simp [he]) rfl
    (by simp [ha]) le_rfl (by omega)
  have hq := Nat.div_le_self A (2 ^ D)
  have e4 := parQ_spec cap (A / 2 ^ D) { s with d := 0 + D, t := 0, e := 0, a := A / 2 ^ D } rfl
    (by simp only; omega) (by omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) (w_eq ?_) ?_
  · obtain ⟨⟩ := s; simp only at hd ht he hp ⊢; pst_rec
  · unfold bitDCost
    omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
