import Proof.Wire_3_5.Primitive.SeedFix.C4SD

/-! # C4 per-call setup (item 3), part 5: the rulers' derived numbers

P3:3011-3016 and C4Dock's rulers (`C4Arm.Nums`: `ℓ, kh, TWd, Cap, 2kh, 2kh + TWd, 8ℓ(2ℓ+1) + Cap, w + 1,
w + TWd + 1, 8ℓ`) and constants (`frame (binary ℓ (Q − 1))`, `frame (binary ℓ 1)`): from the seed's numbers and the
free numbers (`TWd` in `FB 0`, `Cap` in `FB 1`), a register program on registers `140 … 176` leaves

* `2kh + TWd` in `DD 0`, `8ℓ(2ℓ+1) + Cap` in `DD 1`, `w + 1` in `DD 2`, `w + 1 + TWd` in `DD 3`, `8ℓ` in `DD 4`,
  `Q − 1` in `DD 5`, `ℓ − 1` in `DD 6`, and the payload block `RB` (`RB 0 = Q − 1`, `RB 4 = ℓ`, `RB 7` the counter of
  `frame (binary ℓ (Q − 1))`'s stream).

* the blocks `FB`, `DD`, `MB`, `MC`, `RB`; `segG1 … segG3`, their specs, `derW`, **`der_spec`**.

Paper quantities of the main type: the enumeration's rulers and the generator's words at the call's `ℓ`, `kh`, `Q`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

/-- The free numbers' block (`TWd, Cap, Q', h, m, pr, ρ`). -/
def FB : Fin 7 ↪ Fin LNR := blk 130 7 (by norm_num)
def DD : Fin 7 ↪ Fin LNR := blk 140 7 (by norm_num)
def MB : Fin 5 ↪ Fin LNR := blk 150 5 (by norm_num)
def MC : Fin 5 ↪ Fin LNR := blk 160 5 (by norm_num)
def rT1 : Fin LNR := ⟨155, by decide⟩

/-- The payload block of `frame (binary ℓ (Q − 1))` (its counter register `211`). -/
def RB : Fin 8 ↪ Fin LNR := ⟨![⟨170, by decide⟩, ⟨171, by decide⟩, ⟨172, by decide⟩, ⟨173, by decide⟩, ⟨174, by decide⟩,
  ⟨175, by decide⟩, ⟨176, by decide⟩, ⟨211, by decide⟩], by decide⟩

/-- The derived segments' capacity bounds. -/
structure DerCap (cap Q kh tw cp' : ℕ) : Prop where
  c1 : kh + kh + tw ≤ cap
  c2 : max (kh + kh) (Nat.clog 2 Q) * 8 * (max (kh + kh) (Nat.clog 2 Q) + max (kh + kh) (Nat.clog 2 Q) + 1) + cp' ≤ cap
  c3 : wOf kh Q + 1 + tw ≤ cap
  c4 : Q + 2 ≤ cap
  c5 : tw ≤ cap
  c6 : cp' ≤ cap
  c7 : 16 ≤ cap

/-- Derived segment G1. -/
def segG1 : WM (LNS 0) LNR := (.seq (cp (X 0) (DD 0)) (.seq (addTo (FB 0) (DD 0) rT0) (.seq (cp (X 2) (MB 0)) (.seq (StarNums.incN (MB 1) 8) (.seq (SparseNum.mulByW MB) (.seq (cp (MB 0) (DD 4)) (.seq (cp (X 2) rT1) (addTo (X 2) rT1 rT0))))))))

theorem segG1_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh tw cp' : ℕ) (eX0 : s0.val (X 0) = (kh + kh)) (eX2 : s0.val (X 2) = (max (kh + kh) (Nat.clog 2 Q))) (eF0 : s0.val (FB 0) = tw)
    (hzs : ∀ q : Fin LNR, q.val ∈ ([140, 144, 150, 151, 152, 153, 154, 155] : List ℕ) → s0.val q = 0) (hT : s0.val rT0 = 0)
    (hc : DerCap cap Q kh tw cp') :
    ∃ τ c, WExec cap segG1 s0 τ c ∧ c ≤ 60 * UnaryPow.sq cap ∧ τ.val (DD 0) = (kh + kh + tw) ∧ τ.val (DD 4) = ((max (kh + kh) (Nat.clog 2 Q)) * 8) ∧ τ.val rT1 = ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q))) ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, q.val ∉ ([140, 144, 150, 151, 155] : List ℕ) → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
  have hsq := UnaryPow.sq_ge cap
  have hlin := UnaryPow.lin_le_sq cap
  have hlQ : Nat.clog 2 Q ≤ Q := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have cmx : max (kh + kh) (Nat.clog 2 Q) ≤ cap := max_le (by omega) (by omega)
  have cm8 : max (kh + kh) (Nat.clog 2 Q) * 8 ≤ cap := by nlinarith
  obtain ⟨s1, hs1⟩ : ∃ z : WState (LNS 0) LNR, z = (s0).setv (DD 0) (kh + kh) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ z : WState (LNS 0) LNR, z = (s1).setv (DD 0) (kh + kh + tw) := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ z : WState (LNS 0) LNR, z = (s2).setv (MB 0) (max (kh + kh) (Nat.clog 2 Q)) := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ z : WState (LNS 0) LNR, z = (s3).setv (MB 1) 8 := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ z : WState (LNS 0) LNR, z = (s4).setv (MB 0) ((max (kh + kh) (Nat.clog 2 Q)) * 8) := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ z : WState (LNS 0) LNR, z = (s5).setv (DD 4) ((max (kh + kh) (Nat.clog 2 Q)) * 8) := ⟨_, rfl⟩
  obtain ⟨s7, hs7⟩ : ∃ z : WState (LNS 0) LNR, z = (s6).setv rT1 (max (kh + kh) (Nat.clog 2 Q)) := ⟨_, rfl⟩
  obtain ⟨s8, hs8⟩ : ∃ z : WState (LNS 0) LNR, z = (s7).setv rT1 ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q))) := ⟨_, rfl⟩
  have h1 : WExec cap (cp (X 0) (DD 0)) s0 s1 (18 * (kh + kh) + 3) := by
    have ex : s0.val (X 0) = (kh + kh) := eX0
    have w := wc cap (X 0) (DD 0) s0 (by decide) (by decide) (by decide) (hzs _ (by decide)) (hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs1]; exact w
  have h2 : WExec cap (addTo (FB 0) (DD 0) rT0) s1 s2 (18 * tw + 3) := by
    have ep : s1.val (FB 0) = tw := by rw [hs1, vsv, if_neg (show ¬ ((FB 0) = (DD 0)) by decide), eF0]
    have ev : s1.val (DD 0) = (kh + kh) := by rw [hs1, vsv, if_pos rfl]
    have w := ParseNat.addTo_spec cap (FB 0) (DD 0) rT0 (by decide) (by decide) (by decide) s1 (by rw [hs1, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide)]; exact hT) (by rw [ep]; omega) (by rw [ep, ev]; omega)
    rw [ep, ev] at w; rw [hs2]; exact w
  have h3 : WExec cap (cp (X 2) (MB 0)) s2 s3 (18 * (max (kh + kh) (Nat.clog 2 Q)) + 3) := by
    have ex : s2.val (X 2) = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs2, vsv, if_neg (show ¬ ((X 2) = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ ((X 2) = (DD 0)) by decide), eX2]
    have w := wc cap (X 2) (MB 0) s2 (by decide) (by decide) (by decide) (by rw [hs2, vsv, if_neg (show ¬ ((MB 0) = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ ((MB 0) = (DD 0)) by decide)]; exact hzs _ (by decide)) (by rw [hs2, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs3]; exact w
  have h4 : WExec cap (StarNums.incN (MB 1) 8) s3 s4 (4 * 8) := by
    have ex : s3.val (MB 1) = 0 := by rw [hs3, vsv, if_neg (show ¬ ((MB 1) = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MB 1) = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ ((MB 1) = (DD 0)) by decide)]; exact hzs _ (by decide)
    have w := StarNums.incN_spec cap (MB 1) 8 s3 (by rw [ex]; omega)
    rw [ex, Nat.zero_add] at w; rw [hs4]; exact w
  have h5 : WExec cap (SparseNum.mulByW MB) s4 s5 (3 * UnaryPow.sq cap) := by
    have e0 : s4.val (MB 0) = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs4, vsv, if_neg (show ¬ ((MB 0) = (MB 1)) by decide), hs3, vsv, if_pos rfl]
    have e1 : s4.val (MB 1) = 8 := by rw [hs4, vsv, if_pos rfl]
    have w := SparseNum.mulByW_spec cap MB s4 (by rw [hs4, vsv, if_neg (show ¬ ((MB 2) = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ ((MB 2) = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MB 2) = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ ((MB 2) = (DD 0)) by decide)]; exact hzs _ (by decide)) (by rw [hs4, vsv, if_neg (show ¬ ((MB 3) = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ ((MB 3) = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MB 3) = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ ((MB 3) = (DD 0)) by decide)]; exact hzs _ (by decide)) (by rw [hs4, vsv, if_neg (show ¬ ((MB 4) = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ ((MB 4) = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MB 4) = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ ((MB 4) = (DD 0)) by decide)]; exact hzs _ (by decide)) (by rw [e0, e1]; omega) (by rw [e0]; omega) (by rw [e1]; omega)
    rw [e0, e1] at w; rw [hs5]; exact w
  have h6 : WExec cap (cp (MB 0) (DD 4)) s5 s6 (18 * ((max (kh + kh) (Nat.clog 2 Q)) * 8) + 3) := by
    have ex : s5.val (MB 0) = ((max (kh + kh) (Nat.clog 2 Q)) * 8) := by rw [hs5, vsv, if_pos rfl]
    have w := wc cap (MB 0) (DD 4) s5 (by decide) (by decide) (by decide) (by rw [hs5, vsv, if_neg (show ¬ ((DD 4) = (MB 0)) by decide), hs4, vsv, if_neg (show ¬ ((DD 4) = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ ((DD 4) = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ ((DD 4) = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ ((DD 4) = (DD 0)) by decide)]; exact hzs _ (by decide)) (by rw [hs5, vsv, if_neg (show ¬ (rT0 = (MB 0)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs6]; exact w
  have h7 : WExec cap (cp (X 2) rT1) s6 s7 (18 * (max (kh + kh) (Nat.clog 2 Q)) + 3) := by
    have ex : s6.val (X 2) = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs6, vsv, if_neg (show ¬ ((X 2) = (DD 4)) by decide), hs5, vsv, if_neg (show ¬ ((X 2) = (MB 0)) by decide), hs4, vsv, if_neg (show ¬ ((X 2) = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ ((X 2) = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ ((X 2) = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ ((X 2) = (DD 0)) by decide), eX2]
    have w := wc cap (X 2) rT1 s6 (by decide) (by decide) (by decide) (by rw [hs6, vsv, if_neg (show ¬ (rT1 = (DD 4)) by decide), hs5, vsv, if_neg (show ¬ (rT1 = (MB 0)) by decide), hs4, vsv, if_neg (show ¬ (rT1 = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ (rT1 = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT1 = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ (rT1 = (DD 0)) by decide)]; exact hzs _ (by decide)) (by rw [hs6, vsv, if_neg (show ¬ (rT0 = (DD 4)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (MB 0)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs7]; exact w
  have h8 : WExec cap (addTo (X 2) rT1 rT0) s7 s8 (18 * (max (kh + kh) (Nat.clog 2 Q)) + 3) := by
    have ep : s7.val (X 2) = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs7, vsv, if_neg (show ¬ ((X 2) = rT1) by decide), hs6, vsv, if_neg (show ¬ ((X 2) = (DD 4)) by decide), hs5, vsv, if_neg (show ¬ ((X 2) = (MB 0)) by decide), hs4, vsv, if_neg (show ¬ ((X 2) = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ ((X 2) = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ ((X 2) = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ ((X 2) = (DD 0)) by decide), eX2]
    have ev : s7.val rT1 = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs7, vsv, if_pos rfl]
    have w := ParseNat.addTo_spec cap (X 2) rT1 rT0 (by decide) (by decide) (by decide) s7 (by rw [hs7, vsv, if_neg (show ¬ (rT0 = rT1) by decide), hs6, vsv, if_neg (show ¬ (rT0 = (DD 4)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (MB 0)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide)]; exact hT) (by rw [ep]; omega) (by rw [ep, ev]; omega)
    rw [ep, ev] at w; rw [hs8]; exact w
  have f0 : s8.val (DD 0) = (kh + kh + tw) := by rw [hs8, vsv, if_neg (show ¬ ((DD 0) = rT1) by decide), hs7, vsv, if_neg (show ¬ ((DD 0) = rT1) by decide), hs6, vsv, if_neg (show ¬ ((DD 0) = (DD 4)) by decide), hs5, vsv, if_neg (show ¬ ((DD 0) = (MB 0)) by decide), hs4, vsv, if_neg (show ¬ ((DD 0) = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ ((DD 0) = (MB 0)) by decide), hs2, vsv, if_pos rfl]
  have f1 : s8.val (DD 4) = ((max (kh + kh) (Nat.clog 2 Q)) * 8) := by rw [hs8, vsv, if_neg (show ¬ ((DD 4) = rT1) by decide), hs7, vsv, if_neg (show ¬ ((DD 4) = rT1) by decide), hs6, vsv, if_pos rfl]
  have f2 : s8.val rT1 = ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q))) := by rw [hs8, vsv, if_pos rfl]
  have fT : s8.val rT0 = 0 := by rw [hs8, vsv, if_neg (show ¬ (rT0 = rT1) by decide), hs7, vsv, if_neg (show ¬ (rT0 = rT1) by decide), hs6, vsv, if_neg (show ¬ (rT0 = (DD 4)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (MB 0)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (MB 1)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (MB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (DD 0)) by decide)]; exact hT
  refine ⟨s8, _, WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 (WExec.seq h6 (WExec.seq h7 (h8))))))), ?_, f0, f1, f2, fT, fun q hq => ?_, ?_, ?_, ?_⟩
  · have e3 : ∀ x y : ℕ, 18 * (x * y) = 18 * x * y := fun x y => by ring
    omega
  · have nq : ∀ r' : Fin LNR, r'.val ∈ ([140, 144, 150, 151, 155] : List ℕ) → q ≠ r' := fun r' h e => by subst e; exact hq h
    rw [hs8, vsv, if_neg (nq rT1 (by decide)), hs7, vsv, if_neg (nq rT1 (by decide)), hs6, vsv, if_neg (nq (DD 4) (by decide)), hs5, vsv, if_neg (nq (MB 0) (by decide)), hs4, vsv, if_neg (nq (MB 1) (by decide)), hs3, vsv, if_neg (nq (MB 0) (by decide)), hs2, vsv, if_neg (nq (DD 0) (by decide)), hs1, vsv, if_neg (nq (DD 0) (by decide))]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]

/-- Derived segment G2. -/
def segG2 : WM (LNS 0) LNR := (.seq (.inc rT1) (.seq (cp (DD 4) (MC 0)) (.seq (cp rT1 (MC 1)) (.seq (SparseNum.mulByW MC) (.seq (cp (MC 0) (DD 1)) (.seq (addTo (FB 1) (DD 1) rT0) (.seq (cp (WB 0) (DD 2)) (.inc (DD 2)))))))))

theorem segG2_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh tw cp' : ℕ) (eT0 : s0.val rT1 = ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)))) (eD4 : s0.val (DD 4) = ((max (kh + kh) (Nat.clog 2 Q)) * 8)) (eF1 : s0.val (FB 1) = cp') (eW0 : s0.val (WB 0) = (wOf kh Q))
    (hzs : ∀ q : Fin LNR, q.val ∈ ([141, 142, 160, 161, 162, 163, 164] : List ℕ) → s0.val q = 0) (hT : s0.val rT0 = 0)
    (hc : DerCap cap Q kh tw cp') :
    ∃ τ c, WExec cap segG2 s0 τ c ∧ c ≤ 60 * UnaryPow.sq cap ∧ τ.val (DD 1) = ((max (kh + kh) (Nat.clog 2 Q)) * 8 * ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1) + cp') ∧ τ.val (DD 2) = (wOf kh Q + 1) ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, q.val ∉ ([141, 142, 155, 160, 161] : List ℕ) → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
  have hsq := UnaryPow.sq_ge cap
  have hlin := UnaryPow.lin_le_sq cap
  have hlQ : Nat.clog 2 Q ≤ Q := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have cmx : max (kh + kh) (Nat.clog 2 Q) ≤ cap := max_le (by omega) (by omega)
  have cm8 : max (kh + kh) (Nat.clog 2 Q) * 8 ≤ cap := by nlinarith
  obtain ⟨s1, hs1⟩ : ∃ z : WState (LNS 0) LNR, z = (s0).setv rT1 ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ z : WState (LNS 0) LNR, z = (s1).setv (MC 0) ((max (kh + kh) (Nat.clog 2 Q)) * 8) := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ z : WState (LNS 0) LNR, z = (s2).setv (MC 1) ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1) := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ z : WState (LNS 0) LNR, z = (s3).setv (MC 0) ((max (kh + kh) (Nat.clog 2 Q)) * 8 * ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1)) := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ z : WState (LNS 0) LNR, z = (s4).setv (DD 1) ((max (kh + kh) (Nat.clog 2 Q)) * 8 * ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1)) := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ z : WState (LNS 0) LNR, z = (s5).setv (DD 1) ((max (kh + kh) (Nat.clog 2 Q)) * 8 * ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1) + cp') := ⟨_, rfl⟩
  obtain ⟨s7, hs7⟩ : ∃ z : WState (LNS 0) LNR, z = (s6).setv (DD 2) (wOf kh Q) := ⟨_, rfl⟩
  obtain ⟨s8, hs8⟩ : ∃ z : WState (LNS 0) LNR, z = (s7).setv (DD 2) (wOf kh Q + 1) := ⟨_, rfl⟩
  have h1 : WExec cap (.inc rT1) s0 s1 3 := by
    have ex : s0.val rT1 = ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q))) := eT0
    have w := WExec.inc (cap := cap) rT1 s0 (by rw [ex]; omega)
    rw [ex] at w; rw [hs1]; exact w
  have h2 : WExec cap (cp (DD 4) (MC 0)) s1 s2 (18 * ((max (kh + kh) (Nat.clog 2 Q)) * 8) + 3) := by
    have ex : s1.val (DD 4) = ((max (kh + kh) (Nat.clog 2 Q)) * 8) := by rw [hs1, vsv, if_neg (show ¬ ((DD 4) = rT1) by decide), eD4]
    have w := wc cap (DD 4) (MC 0) s1 (by decide) (by decide) (by decide) (by rw [hs1, vsv, if_neg (show ¬ ((MC 0) = rT1) by decide)]; exact hzs _ (by decide)) (by rw [hs1, vsv, if_neg (show ¬ (rT0 = rT1) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs2]; exact w
  have h3 : WExec cap (cp rT1 (MC 1)) s2 s3 (18 * ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1) + 3) := by
    have ex : s2.val rT1 = ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1) := by rw [hs2, vsv, if_neg (show ¬ (rT1 = (MC 0)) by decide), hs1, vsv, if_pos rfl]
    have w := wc cap rT1 (MC 1) s2 (by decide) (by decide) (by decide) (by rw [hs2, vsv, if_neg (show ¬ ((MC 1) = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ ((MC 1) = rT1) by decide)]; exact hzs _ (by decide)) (by rw [hs2, vsv, if_neg (show ¬ (rT0 = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = rT1) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs3]; exact w
  have h4 : WExec cap (SparseNum.mulByW MC) s3 s4 (3 * UnaryPow.sq cap) := by
    have e0 : s3.val (MC 0) = ((max (kh + kh) (Nat.clog 2 Q)) * 8) := by rw [hs3, vsv, if_neg (show ¬ ((MC 0) = (MC 1)) by decide), hs2, vsv, if_pos rfl]
    have e1 : s3.val (MC 1) = ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1) := by rw [hs3, vsv, if_pos rfl]
    have w := SparseNum.mulByW_spec cap MC s3 (by rw [hs3, vsv, if_neg (show ¬ ((MC 2) = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ ((MC 2) = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ ((MC 2) = rT1) by decide)]; exact hzs _ (by decide)) (by rw [hs3, vsv, if_neg (show ¬ ((MC 3) = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ ((MC 3) = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ ((MC 3) = rT1) by decide)]; exact hzs _ (by decide)) (by rw [hs3, vsv, if_neg (show ¬ ((MC 4) = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ ((MC 4) = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ ((MC 4) = rT1) by decide)]; exact hzs _ (by decide)) (by rw [e0, e1]; omega) (by rw [e0]; omega) (by rw [e1]; omega)
    rw [e0, e1] at w; rw [hs4]; exact w
  have h5 : WExec cap (cp (MC 0) (DD 1)) s4 s5 (18 * ((max (kh + kh) (Nat.clog 2 Q)) * 8 * ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1)) + 3) := by
    have ex : s4.val (MC 0) = ((max (kh + kh) (Nat.clog 2 Q)) * 8 * ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1)) := by rw [hs4, vsv, if_pos rfl]
    have w := wc cap (MC 0) (DD 1) s4 (by decide) (by decide) (by decide) (by rw [hs4, vsv, if_neg (show ¬ ((DD 1) = (MC 0)) by decide), hs3, vsv, if_neg (show ¬ ((DD 1) = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ ((DD 1) = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ ((DD 1) = rT1) by decide)]; exact hzs _ (by decide)) (by rw [hs4, vsv, if_neg (show ¬ (rT0 = (MC 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = rT1) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs5]; exact w
  have h6 : WExec cap (addTo (FB 1) (DD 1) rT0) s5 s6 (18 * cp' + 3) := by
    have ep : s5.val (FB 1) = cp' := by rw [hs5, vsv, if_neg (show ¬ ((FB 1) = (DD 1)) by decide), hs4, vsv, if_neg (show ¬ ((FB 1) = (MC 0)) by decide), hs3, vsv, if_neg (show ¬ ((FB 1) = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ ((FB 1) = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ ((FB 1) = rT1) by decide), eF1]
    have ev : s5.val (DD 1) = ((max (kh + kh) (Nat.clog 2 Q)) * 8 * ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1)) := by rw [hs5, vsv, if_pos rfl]
    have w := ParseNat.addTo_spec cap (FB 1) (DD 1) rT0 (by decide) (by decide) (by decide) s5 (by rw [hs5, vsv, if_neg (show ¬ (rT0 = (DD 1)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (MC 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = rT1) by decide)]; exact hT) (by rw [ep]; omega) (by rw [ep, ev]; omega)
    rw [ep, ev] at w; rw [hs6]; exact w
  have h7 : WExec cap (cp (WB 0) (DD 2)) s6 s7 (18 * (wOf kh Q) + 3) := by
    have ex : s6.val (WB 0) = (wOf kh Q) := by rw [hs6, vsv, if_neg (show ¬ ((WB 0) = (DD 1)) by decide), hs5, vsv, if_neg (show ¬ ((WB 0) = (DD 1)) by decide), hs4, vsv, if_neg (show ¬ ((WB 0) = (MC 0)) by decide), hs3, vsv, if_neg (show ¬ ((WB 0) = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ ((WB 0) = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ ((WB 0) = rT1) by decide), eW0]
    have w := wc cap (WB 0) (DD 2) s6 (by decide) (by decide) (by decide) (by rw [hs6, vsv, if_neg (show ¬ ((DD 2) = (DD 1)) by decide), hs5, vsv, if_neg (show ¬ ((DD 2) = (DD 1)) by decide), hs4, vsv, if_neg (show ¬ ((DD 2) = (MC 0)) by decide), hs3, vsv, if_neg (show ¬ ((DD 2) = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ ((DD 2) = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ ((DD 2) = rT1) by decide)]; exact hzs _ (by decide)) (by rw [hs6, vsv, if_neg (show ¬ (rT0 = (DD 1)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (DD 1)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (MC 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = rT1) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs7]; exact w
  have h8 : WExec cap (.inc (DD 2)) s7 s8 3 := by
    have ex : s7.val (DD 2) = (wOf kh Q) := by rw [hs7, vsv, if_pos rfl]
    have w := WExec.inc (cap := cap) (DD 2) s7 (by rw [ex]; omega)
    rw [ex] at w; rw [hs8]; exact w
  have f0 : s8.val (DD 1) = ((max (kh + kh) (Nat.clog 2 Q)) * 8 * ((max (kh + kh) (Nat.clog 2 Q)) + (max (kh + kh) (Nat.clog 2 Q)) + 1) + cp') := by rw [hs8, vsv, if_neg (show ¬ ((DD 1) = (DD 2)) by decide), hs7, vsv, if_neg (show ¬ ((DD 1) = (DD 2)) by decide), hs6, vsv, if_pos rfl]
  have f1 : s8.val (DD 2) = (wOf kh Q + 1) := by rw [hs8, vsv, if_pos rfl]
  have fT : s8.val rT0 = 0 := by rw [hs8, vsv, if_neg (show ¬ (rT0 = (DD 2)) by decide), hs7, vsv, if_neg (show ¬ (rT0 = (DD 2)) by decide), hs6, vsv, if_neg (show ¬ (rT0 = (DD 1)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (DD 1)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (MC 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (MC 1)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (MC 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = rT1) by decide)]; exact hT
  refine ⟨s8, _, WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 (WExec.seq h6 (WExec.seq h7 (h8))))))), ?_, f0, f1, fT, fun q hq => ?_, ?_, ?_, ?_⟩
  · have e3 : ∀ x y : ℕ, 18 * (x * y) = 18 * x * y := fun x y => by ring
    omega
  · have nq : ∀ r' : Fin LNR, r'.val ∈ ([141, 142, 155, 160, 161] : List ℕ) → q ≠ r' := fun r' h e => by subst e; exact hq h
    rw [hs8, vsv, if_neg (nq (DD 2) (by decide)), hs7, vsv, if_neg (nq (DD 2) (by decide)), hs6, vsv, if_neg (nq (DD 1) (by decide)), hs5, vsv, if_neg (nq (DD 1) (by decide)), hs4, vsv, if_neg (nq (MC 0) (by decide)), hs3, vsv, if_neg (nq (MC 1) (by decide)), hs2, vsv, if_neg (nq (MC 0) (by decide)), hs1, vsv, if_neg (nq rT1 (by decide))]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]

/-- Derived segment G3. -/
def segG3 : WM (LNS 0) LNR := (.seq (cp (DD 2) (DD 3)) (.seq (addTo (FB 0) (DD 3) rT0) (.seq (cp (KB 52) (DD 5)) (.seq (.dec (DD 5)) (.seq (cp (X 2) (DD 6)) (.seq (.dec (DD 6)) (.seq (cp (DD 5) (RB 0)) (cp (X 2) (RB 4)))))))))

theorem segG3_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh tw cp' : ℕ) (eD2 : s0.val (DD 2) = (wOf kh Q + 1)) (eF0 : s0.val (FB 0) = tw) (eQ : s0.val (KB 52) = Q) (eX2 : s0.val (X 2) = (max (kh + kh) (Nat.clog 2 Q)))
    (hzs : ∀ q : Fin LNR, q.val ∈ ([143, 145, 146, 170, 174] : List ℕ) → s0.val q = 0) (hT : s0.val rT0 = 0)
    (hc : DerCap cap Q kh tw cp') :
    ∃ τ c, WExec cap segG3 s0 τ c ∧ c ≤ 60 * UnaryPow.sq cap ∧ τ.val (DD 3) = (wOf kh Q + 1 + tw) ∧ τ.val (DD 5) = (Q - 1) ∧ τ.val (DD 6) = ((max (kh + kh) (Nat.clog 2 Q)) - 1) ∧ τ.val (RB 0) = (Q - 1) ∧ τ.val (RB 4) = (max (kh + kh) (Nat.clog 2 Q)) ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, q.val ∉ ([143, 145, 146, 170, 174] : List ℕ) → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
  have hsq := UnaryPow.sq_ge cap
  have hlin := UnaryPow.lin_le_sq cap
  have hlQ : Nat.clog 2 Q ≤ Q := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have cmx : max (kh + kh) (Nat.clog 2 Q) ≤ cap := max_le (by omega) (by omega)
  have cm8 : max (kh + kh) (Nat.clog 2 Q) * 8 ≤ cap := by nlinarith
  obtain ⟨s1, hs1⟩ : ∃ z : WState (LNS 0) LNR, z = (s0).setv (DD 3) (wOf kh Q + 1) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ z : WState (LNS 0) LNR, z = (s1).setv (DD 3) (wOf kh Q + 1 + tw) := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ z : WState (LNS 0) LNR, z = (s2).setv (DD 5) Q := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ z : WState (LNS 0) LNR, z = (s3).setv (DD 5) (Q - 1) := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ z : WState (LNS 0) LNR, z = (s4).setv (DD 6) (max (kh + kh) (Nat.clog 2 Q)) := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ z : WState (LNS 0) LNR, z = (s5).setv (DD 6) ((max (kh + kh) (Nat.clog 2 Q)) - 1) := ⟨_, rfl⟩
  obtain ⟨s7, hs7⟩ : ∃ z : WState (LNS 0) LNR, z = (s6).setv (RB 0) (Q - 1) := ⟨_, rfl⟩
  obtain ⟨s8, hs8⟩ : ∃ z : WState (LNS 0) LNR, z = (s7).setv (RB 4) (max (kh + kh) (Nat.clog 2 Q)) := ⟨_, rfl⟩
  have h1 : WExec cap (cp (DD 2) (DD 3)) s0 s1 (18 * (wOf kh Q + 1) + 3) := by
    have ex : s0.val (DD 2) = (wOf kh Q + 1) := eD2
    have w := wc cap (DD 2) (DD 3) s0 (by decide) (by decide) (by decide) (hzs _ (by decide)) (hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs1]; exact w
  have h2 : WExec cap (addTo (FB 0) (DD 3) rT0) s1 s2 (18 * tw + 3) := by
    have ep : s1.val (FB 0) = tw := by rw [hs1, vsv, if_neg (show ¬ ((FB 0) = (DD 3)) by decide), eF0]
    have ev : s1.val (DD 3) = (wOf kh Q + 1) := by rw [hs1, vsv, if_pos rfl]
    have w := ParseNat.addTo_spec cap (FB 0) (DD 3) rT0 (by decide) (by decide) (by decide) s1 (by rw [hs1, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide)]; exact hT) (by rw [ep]; omega) (by rw [ep, ev]; omega)
    rw [ep, ev] at w; rw [hs2]; exact w
  have h3 : WExec cap (cp (KB 52) (DD 5)) s2 s3 (18 * Q + 3) := by
    have ex : s2.val (KB 52) = Q := by rw [hs2, vsv, if_neg (show ¬ ((KB 52) = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ ((KB 52) = (DD 3)) by decide), eQ]
    have w := wc cap (KB 52) (DD 5) s2 (by decide) (by decide) (by decide) (by rw [hs2, vsv, if_neg (show ¬ ((DD 5) = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ ((DD 5) = (DD 3)) by decide)]; exact hzs _ (by decide)) (by rw [hs2, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs3]; exact w
  have h4 : WExec cap (.dec (DD 5)) s3 s4 1 := by
    have ex : s3.val (DD 5) = Q := by rw [hs3, vsv, if_pos rfl]
    have w := WExec.dec (cap := cap) (DD 5) s3 (by rw [ex]; omega)
    rw [ex] at w; rw [hs4]; exact w
  have h5 : WExec cap (cp (X 2) (DD 6)) s4 s5 (18 * (max (kh + kh) (Nat.clog 2 Q)) + 3) := by
    have ex : s4.val (X 2) = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs4, vsv, if_neg (show ¬ ((X 2) = (DD 5)) by decide), hs3, vsv, if_neg (show ¬ ((X 2) = (DD 5)) by decide), hs2, vsv, if_neg (show ¬ ((X 2) = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ ((X 2) = (DD 3)) by decide), eX2]
    have w := wc cap (X 2) (DD 6) s4 (by decide) (by decide) (by decide) (by rw [hs4, vsv, if_neg (show ¬ ((DD 6) = (DD 5)) by decide), hs3, vsv, if_neg (show ¬ ((DD 6) = (DD 5)) by decide), hs2, vsv, if_neg (show ¬ ((DD 6) = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ ((DD 6) = (DD 3)) by decide)]; exact hzs _ (by decide)) (by rw [hs4, vsv, if_neg (show ¬ (rT0 = (DD 5)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (DD 5)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs5]; exact w
  have h6 : WExec cap (.dec (DD 6)) s5 s6 1 := by
    have ex : s5.val (DD 6) = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs5, vsv, if_pos rfl]
    have w := WExec.dec (cap := cap) (DD 6) s5 (by rw [ex]; omega)
    rw [ex] at w; rw [hs6]; exact w
  have h7 : WExec cap (cp (DD 5) (RB 0)) s6 s7 (18 * (Q - 1) + 3) := by
    have ex : s6.val (DD 5) = (Q - 1) := by rw [hs6, vsv, if_neg (show ¬ ((DD 5) = (DD 6)) by decide), hs5, vsv, if_neg (show ¬ ((DD 5) = (DD 6)) by decide), hs4, vsv, if_pos rfl]
    have w := wc cap (DD 5) (RB 0) s6 (by decide) (by decide) (by decide) (by rw [hs6, vsv, if_neg (show ¬ ((RB 0) = (DD 6)) by decide), hs5, vsv, if_neg (show ¬ ((RB 0) = (DD 6)) by decide), hs4, vsv, if_neg (show ¬ ((RB 0) = (DD 5)) by decide), hs3, vsv, if_neg (show ¬ ((RB 0) = (DD 5)) by decide), hs2, vsv, if_neg (show ¬ ((RB 0) = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ ((RB 0) = (DD 3)) by decide)]; exact hzs _ (by decide)) (by rw [hs6, vsv, if_neg (show ¬ (rT0 = (DD 6)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (DD 6)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (DD 5)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (DD 5)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs7]; exact w
  have h8 : WExec cap (cp (X 2) (RB 4)) s7 s8 (18 * (max (kh + kh) (Nat.clog 2 Q)) + 3) := by
    have ex : s7.val (X 2) = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs7, vsv, if_neg (show ¬ ((X 2) = (RB 0)) by decide), hs6, vsv, if_neg (show ¬ ((X 2) = (DD 6)) by decide), hs5, vsv, if_neg (show ¬ ((X 2) = (DD 6)) by decide), hs4, vsv, if_neg (show ¬ ((X 2) = (DD 5)) by decide), hs3, vsv, if_neg (show ¬ ((X 2) = (DD 5)) by decide), hs2, vsv, if_neg (show ¬ ((X 2) = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ ((X 2) = (DD 3)) by decide), eX2]
    have w := wc cap (X 2) (RB 4) s7 (by decide) (by decide) (by decide) (by rw [hs7, vsv, if_neg (show ¬ ((RB 4) = (RB 0)) by decide), hs6, vsv, if_neg (show ¬ ((RB 4) = (DD 6)) by decide), hs5, vsv, if_neg (show ¬ ((RB 4) = (DD 6)) by decide), hs4, vsv, if_neg (show ¬ ((RB 4) = (DD 5)) by decide), hs3, vsv, if_neg (show ¬ ((RB 4) = (DD 5)) by decide), hs2, vsv, if_neg (show ¬ ((RB 4) = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ ((RB 4) = (DD 3)) by decide)]; exact hzs _ (by decide)) (by rw [hs7, vsv, if_neg (show ¬ (rT0 = (RB 0)) by decide), hs6, vsv, if_neg (show ¬ (rT0 = (DD 6)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (DD 6)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (DD 5)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (DD 5)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs8]; exact w
  have f0 : s8.val (DD 3) = (wOf kh Q + 1 + tw) := by rw [hs8, vsv, if_neg (show ¬ ((DD 3) = (RB 4)) by decide), hs7, vsv, if_neg (show ¬ ((DD 3) = (RB 0)) by decide), hs6, vsv, if_neg (show ¬ ((DD 3) = (DD 6)) by decide), hs5, vsv, if_neg (show ¬ ((DD 3) = (DD 6)) by decide), hs4, vsv, if_neg (show ¬ ((DD 3) = (DD 5)) by decide), hs3, vsv, if_neg (show ¬ ((DD 3) = (DD 5)) by decide), hs2, vsv, if_pos rfl]
  have f1 : s8.val (DD 5) = (Q - 1) := by rw [hs8, vsv, if_neg (show ¬ ((DD 5) = (RB 4)) by decide), hs7, vsv, if_neg (show ¬ ((DD 5) = (RB 0)) by decide), hs6, vsv, if_neg (show ¬ ((DD 5) = (DD 6)) by decide), hs5, vsv, if_neg (show ¬ ((DD 5) = (DD 6)) by decide), hs4, vsv, if_pos rfl]
  have f2 : s8.val (DD 6) = ((max (kh + kh) (Nat.clog 2 Q)) - 1) := by rw [hs8, vsv, if_neg (show ¬ ((DD 6) = (RB 4)) by decide), hs7, vsv, if_neg (show ¬ ((DD 6) = (RB 0)) by decide), hs6, vsv, if_pos rfl]
  have f3 : s8.val (RB 0) = (Q - 1) := by rw [hs8, vsv, if_neg (show ¬ ((RB 0) = (RB 4)) by decide), hs7, vsv, if_pos rfl]
  have f4 : s8.val (RB 4) = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs8, vsv, if_pos rfl]
  have fT : s8.val rT0 = 0 := by rw [hs8, vsv, if_neg (show ¬ (rT0 = (RB 4)) by decide), hs7, vsv, if_neg (show ¬ (rT0 = (RB 0)) by decide), hs6, vsv, if_neg (show ¬ (rT0 = (DD 6)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (DD 6)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (DD 5)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (DD 5)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (DD 3)) by decide)]; exact hT
  refine ⟨s8, _, WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 (WExec.seq h6 (WExec.seq h7 (h8))))))), ?_, f0, f1, f2, f3, f4, fT, fun q hq => ?_, ?_, ?_, ?_⟩
  · have e3 : ∀ x y : ℕ, 18 * (x * y) = 18 * x * y := fun x y => by ring
    omega
  · have nq : ∀ r' : Fin LNR, r'.val ∈ ([143, 145, 146, 170, 174] : List ℕ) → q ≠ r' := fun r' h e => by subst e; exact hq h
    rw [hs8, vsv, if_neg (nq (RB 4) (by decide)), hs7, vsv, if_neg (nq (RB 0) (by decide)), hs6, vsv, if_neg (nq (DD 6) (by decide)), hs5, vsv, if_neg (nq (DD 6) (by decide)), hs4, vsv, if_neg (nq (DD 5) (by decide)), hs3, vsv, if_neg (nq (DD 5) (by decide)), hs2, vsv, if_neg (nq (DD 3) (by decide)), hs1, vsv, if_neg (nq (DD 3) (by decide))]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]

/-- **The rulers' derived numbers** (the three segments). -/
def derW : WM (LNS 0) LNR := .seq segG1 (.seq segG2 segG3)

/-- **The rulers' derived numbers, run.** -/
theorem der_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh tw cp' : ℕ)
    (eX0 : s0.val (X 0) = kh + kh) (eX2 : s0.val (X 2) = max (kh + kh) (Nat.clog 2 Q)) (eF0 : s0.val (FB 0) = tw)
    (eF1 : s0.val (FB 1) = cp') (eW0 : s0.val (WB 0) = wOf kh Q) (eQ : s0.val (KB 52) = Q)
    (hz : ∀ q : Fin LNR, 140 ≤ q.val → q.val < 177 → s0.val q = 0) (hT : s0.val rT0 = 0)
    (hc : DerCap cap Q kh tw cp') :
    ∃ τ c, WExec cap derW s0 τ c ∧ c ≤ 200 * UnaryPow.sq cap ∧
      τ.val (DD 0) = kh + kh + tw ∧
      τ.val (DD 1) = max (kh + kh) (Nat.clog 2 Q) * 8 * (max (kh + kh) (Nat.clog 2 Q) + max (kh + kh) (Nat.clog 2 Q) + 1) + cp' ∧
      τ.val (DD 2) = wOf kh Q + 1 ∧ τ.val (DD 3) = wOf kh Q + 1 + tw ∧
      τ.val (DD 4) = max (kh + kh) (Nat.clog 2 Q) * 8 ∧ τ.val (DD 5) = Q - 1 ∧
      τ.val (DD 6) = max (kh + kh) (Nat.clog 2 Q) - 1 ∧ τ.val (RB 0) = Q - 1 ∧
      τ.val (RB 4) = max (kh + kh) (Nat.clog 2 Q) ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, (q.val < 140 ∨ 177 ≤ q.val) → τ.val q = s0.val q) ∧
      (∀ q : Fin LNR, q.val ∈ ([171, 172, 173, 175, 176] : List ℕ) → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨τ1, c1, h1, c1le, g10, g14, gT0, t1, fr1, st1, sh1, cl1⟩ := segG1_spec cap s0 Q kh tw cp' eX0 eX2 eF0
    (fun q hq => hz q (by simp at hq; omega) (by simp at hq; omega)) hT hc
  have k1 : ∀ q : Fin LNR, q.val ∉ ([140, 144, 150, 151, 155] : List ℕ) → τ1.val q = s0.val q := fr1
  obtain ⟨τ2, c2, h2, c2le, g21, g22, t2, fr2, st2, sh2, cl2⟩ := segG2_spec cap τ1 Q kh tw cp' gT0 g14
    (by rw [k1 _ (by decide)]; exact eF1) (by rw [k1 _ (by decide)]; exact eW0)
    (fun q hq => by rw [k1 q (by simp at hq ⊢; omega)]; exact hz q (by simp at hq; omega) (by simp at hq; omega)) t1 hc
  have k2 : ∀ q : Fin LNR, q.val ∉ ([141, 142, 155, 160, 161] : List ℕ) → τ2.val q = τ1.val q := fr2
  obtain ⟨τ3, c3, h3, c3le, g33, g35, g36, gR0, gR4, t3, fr3, st3, sh3, cl3⟩ := segG3_spec cap τ2 Q kh tw cp' g22
    (by rw [k2 _ (by decide), k1 _ (by decide)]; exact eF0) (by rw [k2 _ (by decide), k1 _ (by decide)]; exact eQ)
    (by rw [k2 _ (by decide), k1 _ (by decide)]; exact eX2)
    (fun q hq => by rw [k2 q (by simp at hq ⊢; omega), k1 q (by simp at hq ⊢; omega)]
                    exact hz q (by simp at hq; omega) (by simp at hq; omega)) t2 hc
  have k3 : ∀ q : Fin LNR, q.val ∉ ([143, 145, 146, 170, 174] : List ℕ) → τ3.val q = τ2.val q := fr3
  refine ⟨τ3, _, WExec.seq h1 (WExec.seq h2 h3), by omega, ?_, ?_, ?_, g33, ?_, g35, g36, gR0, gR4, t3,
    fun q hq => ?_, fun q hq => ?_, ?_, ?_, ?_⟩
  · rw [k3 _ (by decide), k2 _ (by decide)]; exact g10
  · rw [k3 _ (by decide)]; exact g21
  · rw [k3 _ (by decide)]; exact g22
  · rw [k3 _ (by decide), k2 _ (by decide)]; exact g14
  · rw [k3 q (by simp; omega), k2 q (by simp; omega), k1 q (by simp; omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [k3 q (by simp; omega), k2 q (by simp; omega), k1 q (by simp; omega)]
  · rw [st3, st2, st1]
  · rw [sh3, sh2, sh1]
  · rw [cl3, cl2, cl1]

end NearCubicWires.WireExponent3_5.PrimT.C4Set
