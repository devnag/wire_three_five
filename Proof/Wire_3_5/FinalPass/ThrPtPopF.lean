import Proof.Wire_3_5.FinalPass.ThrPtPopE

/-! # S2 (THR per point), part 8: the population builder, whole (P3:2596-2606)

**`popW_spec`**: from the row word `1^p 0 1^{r₀} 0` + the coefficients `1^{a_i} 0` (rest arbitrary), the framed corner
word `frameP X` (`|X| = 4M`, rest arbitrary), and a population stream of `2M + 1` cells ending in `false`, every head
at `0`, the digit `D` and `M` in their registers and the scratch registers `0`: the population stream becomes
`frame (popZ sgn D as X)`; every other stream, every head and every register as at entry.
Paper quantity: the digit population `thrDigitPop` of digit `D` (P3:2598-2599), padded with `0` to `M` entries. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop

variable (cap : ℕ)

/-! ## Rewinds -/

theorem rew_rw (s : PSt) (h : s.hr = s.rwh) (hc : s.hr ≤ cap) :
    WExec cap (WM.rewind 0 6) s.w { s with hr := 0, rwh := 0 }.w (5 * s.hr + 1) := by
  have e := wrewind_spec cap (0 : Fin 3) (6 : Fin 11) s.hr s.w rfl hc
  rw [p_hr, show s.w.sh 0 = s.rwh from rfl, p_rwh] at e
  refine WExec.cast cap e (w_eq ?_) le_rfl
  simp only [PSt.mk.injEq, true_and, and_true]
  omega

theorem rew_x (s : PSt) (h : s.hx = s.xh) (hc : s.hx ≤ cap) :
    WExec cap (WM.rewind 1 7) s.w { s with hx := 0, xh := 0 }.w (5 * s.hx + 1) := by
  have e := wrewind_spec cap (1 : Fin 3) (7 : Fin 11) s.hx s.w rfl hc
  rw [p_hx, show s.w.sh 1 = s.xh from rfl, p_xh] at e
  refine WExec.cast cap e (w_eq ?_) le_rfl
  simp only [PSt.mk.injEq, true_and, and_true]
  omega

theorem rew_z (s : PSt) (h : s.hz = s.zh) (hc : s.hz ≤ cap) :
    WExec cap (WM.rewind 2 8) s.w { s with hz := 0, zh := 0 }.w (5 * s.hz + 1) := by
  have e := wrewind_spec cap (2 : Fin 3) (8 : Fin 11) s.hz s.w rfl hc
  rw [p_hz, show s.w.sh 2 = s.zh from rfl, p_zh] at e
  refine WExec.cast cap e (w_eq ?_) le_rfl
  simp only [PSt.mk.injEq, true_and, and_true]
  omega

/-! ## The builder -/

/-- **The population builder** for sign `sgn` (digit in `D`, occurrence count in `MM`). -/
def popW (sgn : Bool) : PProg :=
  .seq skipU (.seq skipU (.seq copyM (.seq (occLoop sgn) (.seq padLoop (.seq (WM.rewind 0 6)
    (.seq (WM.rewind 1 7) (WM.rewind 2 8)))))))

/-- The builder's capacity. -/
def popCap (p r0 M A0 D : ℕ) : ℕ := p + r0 + 2 + M * (A0 + 1) + A0 + 8 * M + 4 * M + 2 * A0 + 2 * D + 12

/-- The builder's step bound. -/
def popCost (p r0 M A0 D : ℕ) : ℕ :=
  (14 * p + 9) + 1 + ((14 * r0 + 9) + 1 + ((7 * M + 1 + 1 + (M * 15 + 1)) + 1 + ((M * (occCost A0 D + 4) + 1) + 1 +
    ((M * 20 + 1) + 1 + ((5 * (p + r0 + 2 + M * (A0 + 1)) + 1) + 1 + ((5 * (8 * M) + 1) + 1 + (5 * (2 * M) + 1)))))))

theorem sum_succ_le (A0 : ℕ) : ∀ (as : List ℕ), (∀ a ∈ as, a ≤ A0) → (as.map (· + 1)).sum ≤ as.length * (A0 + 1)
  | [], _ => by simp
  | a :: as, h => by
    have h1 := h a (by simp)
    have h2 := sum_succ_le A0 as (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at h2 ⊢
    omega

theorem drop_unary (n : ℕ) (rest : List Bool) : (ListEval.unary n ++ rest).drop (n + 1) = rest :=
  List.drop_left' (by simp [ListEval.unary])

theorem popW_spec (sgn : Bool) (p r0 D A0 : ℕ) (as : List ℕ) (X restR restX zr0 : List Bool) (s : PSt)
    (hrw : s.rw = ListEval.unary p ++ ListEval.unary r0 ++ as.flatMap ListEval.unary ++ restR)
    (hX : s.x = frameP X ++ restX) (hXl : X.length = 4 * as.length) (hZ : s.z = zr0 ++ [false])
    (hzr : zr0.length = 2 * as.length) (hA0 : ∀ a ∈ as, a ≤ A0)
    (hrwh : s.rwh = 0) (hxh : s.xh = 0) (hzh : s.zh = 0) (hhr : s.hr = 0) (hhx : s.hx = 0) (hhz : s.hz = 0)
    (hd : s.d = D) (hmm : s.mm = as.length) (hm : s.m = 0) (ha : s.a = 0) (ht : s.t = 0) (he : s.e = 0)
    (hp : s.pb = 0) (hrem : s.rem = 0) (hc : popCap p r0 as.length A0 D ≤ cap) :
    WExec cap (popW sgn) s.w { s with z := frame (popZ sgn D as X) }.w (popCost p r0 as.length A0 D) := by
  unfold popCap at hc
  have hsum := sum_succ_le A0 as hA0
  have hsel := selB_length_le sgn D as X
  -- skip p
  have r1 : s.rw.drop s.rwh = ListEval.unary p ++ (ListEval.unary r0 ++ (as.flatMap ListEval.unary ++ restR)) := by
    rw [hrw, hrwh]; simp [List.append_assoc]
  have e1 := skipU_spec cap s p (fun k hk => by rw [rd_drop, r1]; exact rd_unary_lt p k _ hk)
    (by rw [rd_drop, r1]; exact rd_unary_end p _) ht (by omega) (by omega)
  obtain ⟨s1, hs1⟩ : ∃ s1 : PSt, s1 = { s with rwh := s.rwh + p + 1, hr := s.hr + p + 1 } := ⟨_, rfl⟩
  rw [← hs1] at e1
  -- skip r₀
  have r2 : s1.rw.drop s1.rwh = ListEval.unary r0 ++ (as.flatMap ListEval.unary ++ restR) := by
    rw [hs1]
    show s.rw.drop (s.rwh + p + 1) = _
    rw [hrwh, Nat.zero_add, hrw, List.append_assoc, List.append_assoc, drop_unary]
  have e2 := skipU_spec cap s1 r0 (fun k hk => by rw [rd_drop, r2]; exact rd_unary_lt r0 k _ hk)
    (by rw [rd_drop, r2]; exact rd_unary_end r0 _) (by rw [hs1]; exact ht) (by rw [hs1]; simp only; omega)
    (by omega)
  obtain ⟨s2, hs2⟩ : ∃ s2 : PSt, s2 = { s1 with rwh := s1.rwh + r0 + 1, hr := s1.hr + r0 + 1 } := ⟨_, rfl⟩
  rw [← hs2] at e2
  -- the counters
  have e3 := copyM_spec cap s2 as.length (by rw [hs2, hs1]; exact hmm) (by rw [hs2, hs1]; exact ht)
    (by rw [hs2, hs1]; exact hm) (by rw [hs2, hs1]; exact hrem) (by omega)
  obtain ⟨s3, hs3⟩ : ∃ s3 : PSt, s3 = { s2 with m := as.length, rem := as.length } := ⟨_, rfl⟩
  rw [← hs3] at e3
  -- the occurrences
  have r3 : s3.rw.drop s3.rwh = as.flatMap ListEval.unary ++ restR := by
    rw [hs3, hs2, hs1]
    show s.rw.drop (s.rwh + p + 1 + r0 + 1) = _
    rw [hrwh, Nat.zero_add, show p + 1 + r0 + 1 = (p + 1) + (r0 + 1) by omega, ← List.drop_drop, hrw,
      List.append_assoc, List.append_assoc, drop_unary, drop_unary]
  have g3x : s3.x = s.x := by rw [hs3, hs2, hs1]
  have g3z : s3.z = s.z := by rw [hs3, hs2, hs1]
  have g3n : s3.xh = 0 ∧ s3.hx = 0 ∧ s3.zh = 0 ∧ s3.hz = 0 ∧ s3.rem = as.length ∧
      s3.m = as.length ∧ s3.d = D ∧ s3.a = 0 ∧ s3.t = 0 ∧ s3.e = 0 ∧ s3.pb = 0 ∧ s3.hr = p + 1 + r0 + 1 ∧
      s3.rwh = p + 1 + r0 + 1 := by
    rw [hs3, hs2, hs1]; simp only [true_and]; omega
  obtain ⟨g1, g2, g3', g4, g5', g6, g7, g8, g9, g10, g11, g12, g13⟩ := g3n
  obtain ⟨zr1, hzr1, e4⟩ := occLoop_spec cap sgn D A0 restR restX (by omega) (by omega) as X [] [] zr0 s3 rfl
    (by simpa using hXl) hA0 r3 (by rw [g3x, hX]; simp) (by rw [g1]; simp) (by omega)
    (by rw [g3z, hZ]; simp [selB]) (by rw [hzr, g5']) (by rw [g3']; simp [selB])
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simp only [List.nil_append, selB, List.length_nil, Nat.add_zero] at hzr1 e4
  obtain ⟨s4, hs4⟩ : ∃ s4 : PSt, s4 = { s3 with
      rwh := s3.rwh + (as.map (· + 1)).sum, hr := s3.hr + (as.map (· + 1)).sum,
      xh := s3.xh + 8 * as.length, hx := s3.xh + 8 * as.length,
      z := frameP (selB sgn D as X) ++ zr1 ++ [false], zh := 2 * (selB sgn D as X).length,
      hz := 2 * (selB sgn D as X).length, rem := s3.rem - (selB sgn D as X).length, m := 0 } := ⟨_, rfl⟩
  rw [← hs4] at e4
  -- the padding
  have e5 := padLoop_spec cap (as.length - (selB sgn D as X).length) s4 (selB sgn D as X) zr1
    (by rw [hs4]; simp only; omega) (by rw [hs4]) (by rw [hzr1]; omega)
    (by rw [hs4, fP_length]) (by rw [hs4]; simp only; omega) (by omega)
  obtain ⟨s5, hs5⟩ : ∃ s5 : PSt, s5 = { s4 with
      z := frameP (selB sgn D as X ++ List.replicate (as.length - (selB sgn D as X).length) false) ++ [false],
      zh := s4.zh + 2 * (as.length - (selB sgn D as X).length),
      hz := s4.hz + 2 * (as.length - (selB sgn D as X).length), rem := 0 } := ⟨_, rfl⟩
  rw [← hs5] at e5
  have g5 : s5.hr = s5.rwh ∧ s5.hx = s5.xh ∧ s5.hz = s5.zh ∧ s5.hr = p + 1 + r0 + 1 + (as.map (· + 1)).sum ∧
      s5.hx = 8 * as.length ∧ s5.hz = 2 * as.length := by
    rw [hs5, hs4]; simp only [true_and]; omega
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := g5
  -- the rewinds
  have e6 := rew_rw cap s5 k1 (by omega)
  have e7 := rew_x cap { s5 with hr := 0, rwh := 0 } k2 (by simp only; omega)
  have e8 := rew_z cap { { s5 with hr := 0, rwh := 0 } with hx := 0, xh := 0 } k3 (by simp only; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) (w_eq ?_) ?_
  · rw [hs5, hs4, hs3, hs2, hs1]
    simp only [popZ, frame_eq_frameP, PSt.mk.injEq, true_and, and_true]
    omega
  · simp only
    rw [k4, k5, k6]
    unfold popCost
    omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
