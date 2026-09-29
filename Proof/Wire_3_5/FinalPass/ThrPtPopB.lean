import Proof.Wire_3_5.FinalPass.ThrPtPopA

/-! # S2 (THR per point), part 4: the population builder's steps (P3:2596-2606)

On the builder's layout (`PSt`): reading a coefficient `a_i` in unary from the row word (`readA`), skipping a unary
number (`skipU`), counted head moves (`incN`, `fwdN`), and the selection step at one occurrence (`selStep`): when the
digit bit is `1`, stage 3's reading tree (`Pop.tree`, verified) reads the occurrence's four framed corners and writes
the marker and the population bit `Z^±` (`popG`) on the population stream; otherwise the corners are skipped.
Main declarations: `tree_rec`, `readA_spec`, `skipU_spec`, **`selStep_spec`**, **`occStep_spec`**. Paper quantity:
one entry `Z_i^±` of the digit population `thrDigitPop` (when `v_{i,d} = 1`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop

theorem fP_length (a : List Bool) : (frameP a).length = 2 * a.length := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [frameP] at ih ⊢; omega

variable (cap : ℕ)

/-! ## Stage 3's tree on the layout -/

theorem tree_rec (sgn : Bool) (s : PSt) (P Q zr rest bs : List Bool) (z0 z1 : Bool) (hl : bs.length = 4)
    (hX : s.x = P ++ frameP bs ++ rest) (hsh : s.xh = P.length) (hZ : s.z = Q ++ z0 :: z1 :: zr)
    (hhZ : s.zh = Q.length) :
    WExec cap (tree 1 2 true (popG sgn) 4 []) s.w
      { s with z := Q ++ true :: popG sgn bs :: zr, xh := s.xh + 8, zh := Q.length + 2 }.w 27 := by
  obtain ⟨τ, e, h1, h2, h3, h4, hF⟩ := tree_spec cap (1 : Fin 3) 2 (by decide) true (popG sgn) rest Q zr z0 z1 4 []
    bs P s.w hl hX hsh hZ hhZ
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · funext i
    fin_cases i
    · exact (hF.1 0 (by decide)).2
    · exact h2
    · exact h4
  · funext i
    fin_cases i
    · exact (hF.1 0 (by decide)).1
    · exact h1
    · show τ.st 2 = Q ++ true :: popG sgn bs :: zr
      simpa using h3
  · funext r
    exact hF.2.1 r (fun h => h)
  · exact hF.2.2

/-! ## Counted moves -/

/-- `k` increments of a register. -/
def incN (r : Fin 11) : ℕ → PProg
  | 0 => .skip
  | k + 1 => .seq (.inc r) (incN r k)

/-- `k` forward moves of a stream. -/
def fwdN (i : Fin 3) : ℕ → PProg
  | 0 => .skip
  | k + 1 => .seq (.fwd i) (fwdN i k)

theorem incN_hx : ∀ (k : ℕ) (s : PSt), s.hx + k ≤ cap → WExec cap (incN 7 k) s.w { s with hx := s.hx + k }.w (5 * k)
  | 0, s, _ => WExec.cast cap (WExec.skip _) (w_eq (by obtain ⟨⟩ := s; rfl)) le_rfl
  | k + 1, s, hc => by
    have e1 := inc_hx cap s (by omega)
    have e2 := incN_hx k { s with hx := s.hx + 1 } (by simp only; omega)
    exact WExec.cast cap (WExec.seq e1 e2) (w_eq (by obtain ⟨⟩ := s; simp only; pst_rec)) (by omega)

theorem incN_hz : ∀ (k : ℕ) (s : PSt), s.hz + k ≤ cap → WExec cap (incN 8 k) s.w { s with hz := s.hz + k }.w (5 * k)
  | 0, s, _ => WExec.cast cap (WExec.skip _) (w_eq (by obtain ⟨⟩ := s; rfl)) le_rfl
  | k + 1, s, hc => by
    have e1 := inc_hz cap s (by omega)
    have e2 := incN_hz k { s with hz := s.hz + 1 } (by simp only; omega)
    exact WExec.cast cap (WExec.seq e1 e2) (w_eq (by obtain ⟨⟩ := s; simp only; pst_rec)) (by omega)

theorem fwdN_x : ∀ (k : ℕ) (s : PSt), WExec cap (fwdN 1 k) s.w { s with xh := s.xh + k }.w (2 * k)
  | 0, s => WExec.cast cap (WExec.skip _) (w_eq (by obtain ⟨⟩ := s; rfl)) le_rfl
  | k + 1, s => by
    have e1 : WExec cap (.fwd 1) s.w { s with xh := s.xh + 1 }.w 1 := by
      have h := WExec.fwd (cap := cap) (1 : Fin 3) s.w
      rwa [show s.w.sh 1 = s.xh from rfl, p_xh] at h
    have e2 := fwdN_x k { s with xh := s.xh + 1 }
    exact WExec.cast cap (WExec.seq e1 e2) (w_eq (by obtain ⟨⟩ := s; simp only; pst_rec)) (by omega)

/-! ## Reading the row word -/

/-- Read `1^a 0` from the row word into `A` (the head counted in `HR`). -/
def readA : PProg := WM.readU 0 6 2

theorem readA_spec (s : PSt) (n : ℕ) (hones : ∀ k < n, readTapeBit s.rw (s.rwh + k) = true)
    (hend : readTapeBit s.rw (s.rwh + n) = false) (hc : s.hr + n + 1 ≤ cap) (hc2 : s.a + n ≤ cap) :
    WExec cap readA s.w { s with rwh := s.rwh + n + 1, hr := s.hr + n + 1, a := s.a + n }.w (11 * n + 7) := by
  have h := wreadU_spec cap (0 : Fin 3) (6 : Fin 11) 2 (by decide) n s.w hones hend hc hc2
  rw [show s.w.sh 0 = s.rwh from rfl, p_rwh, show s.w.val 6 = s.hr from rfl, p_hr, show s.w.val 2 = s.a from rfl,
    p_a] at h
  exact h

/-- Skip `1^n 0` on the row word (through `T`). -/
def skipU : PProg := .seq (WM.readU 0 6 3) (WM.clear 3)

theorem skipU_spec (s : PSt) (n : ℕ) (hones : ∀ k < n, readTapeBit s.rw (s.rwh + k) = true)
    (hend : readTapeBit s.rw (s.rwh + n) = false) (ht : s.t = 0) (hc : s.hr + n + 1 ≤ cap) (hc2 : n ≤ cap) :
    WExec cap skipU s.w { s with rwh := s.rwh + n + 1, hr := s.hr + n + 1 }.w (11 * n + 7 + 1 + (3 * n + 1)) := by
  have h := wreadU_spec cap (0 : Fin 3) (6 : Fin 11) 3 (by decide) n s.w hones hend hc (by show s.t + n ≤ cap; omega)
  rw [show s.w.sh 0 = s.rwh from rfl, p_rwh, show s.w.val 6 = s.hr from rfl, p_hr, show s.w.val 3 = s.t from rfl,
    p_t] at h
  have h2 := wclear_spec cap (3 : Fin 11) n
    ({ { { s with rwh := s.rwh + n + 1 } with hr := s.hr + n + 1 } with t := s.t + n } : PSt).w
    (by show s.t + n = n; omega) (by show s.t + n ≤ cap; omega)
  rw [p_t] at h2
  exact WExec.cast cap (WExec.seq h h2) (w_eq (by obtain ⟨⟩ := s; simp only at ht ⊢; pst_rec)) le_rfl

/-! ## One occurrence -/

/-- **The selection at one occurrence**: when the digit bit is `1`, the corners' population bit is written (marker and
bit) and the population's counters step; otherwise the four corners are skipped. -/
def selStep (sgn : Bool) : PProg :=
  .ifr 4 (.seq (tree 1 2 true (popG sgn) 4 []) (.seq (incN 7 8) (.seq (incN 8 2) (.seq (.dec 9) (.dec 4)))))
    (.seq (fwdN 1 8) (incN 7 8))

theorem selStep_one (sgn : Bool) (s : PSt) (P Q zr rest bs : List Bool) (z0 z1 : Bool) (hl : bs.length = 4)
    (hX : s.x = P ++ frameP bs ++ rest) (hsh : s.xh = P.length) (hZ : s.z = Q ++ z0 :: z1 :: zr)
    (hhZ : s.zh = Q.length) (hp : s.pb = 1) (hrem : 1 ≤ s.rem) (hcx : s.hx + 8 ≤ cap) (hcz : s.hz + 2 ≤ cap)
    (hcr : s.rem ≤ cap) (hc1 : 1 ≤ cap) :
    WExec cap (selStep sgn) s.w
      { s with z := Q ++ true :: popG sgn bs :: zr, xh := s.xh + 8, zh := Q.length + 2, hx := s.hx + 8,
               hz := s.hz + 2, rem := s.rem - 1, pb := 0 }.w 90 := by
  have e1 := tree_rec cap sgn s P Q zr rest bs z0 z1 hl hX hsh hZ hhZ
  have e2 := incN_hx cap 8 { s with z := Q ++ true :: popG sgn bs :: zr, xh := s.xh + 8, zh := Q.length + 2 }
    (by simp only; omega)
  have e3 := incN_hz cap 2 { { s with z := Q ++ true :: popG sgn bs :: zr, xh := s.xh + 8, zh := Q.length + 2 } with
    hx := s.hx + 8 } (by simp only; omega)
  have e4 := dec_rem cap { { { s with z := Q ++ true :: popG sgn bs :: zr, xh := s.xh + 8, zh := Q.length + 2 } with
    hx := s.hx + 8 } with hz := s.hz + 2 } (by simp only; omega)
  have e5 := dec_pb cap { { { { s with z := Q ++ true :: popG sgn bs :: zr, xh := s.xh + 8, zh := Q.length + 2 } with
    hx := s.hx + 8 } with hz := s.hz + 2 } with rem := s.rem - 1 } (by simp only; omega)
  have e := WExec.ifrT (Q := .seq (fwdN 1 8) (incN 7 8)) (show s.w.val 4 ≠ 0 by show s.pb ≠ 0; omega)
    (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))))
  exact WExec.cast cap e (w_eq (by obtain ⟨⟩ := s; simp only at hp ⊢; pst_rec)) (by omega)

theorem selStep_zero (sgn : Bool) (s : PSt) (hp : s.pb = 0) (hcx : s.hx + 8 ≤ cap) :
    WExec cap (selStep sgn) s.w { s with xh := s.xh + 8, hx := s.hx + 8 }.w 58 := by
  have e1 := fwdN_x cap 8 s
  have e2 := incN_hx cap 8 { s with xh := s.xh + 8 } (by simp only; omega)
  have e := WExec.ifrF (P := .seq (tree 1 2 true (popG sgn) 4 []) (.seq (incN 7 8) (.seq (incN 8 2)
    (.seq (.dec 9) (.dec 4))))) (show s.w.val 4 = 0 from hp) (WExec.seq e1 e2)
  exact WExec.cast cap e (w_eq (by obtain ⟨⟩ := s; simp only)) (by omega)

/-- **One occurrence**: its coefficient read, its digit bit, the selection. -/
def occStep (sgn : Bool) : PProg := .seq readA (.seq bitD (selStep sgn))

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
