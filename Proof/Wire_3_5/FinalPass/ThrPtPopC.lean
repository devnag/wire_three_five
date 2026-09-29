import Proof.Wire_3_5.FinalPass.ThrPtPopB
import Proof.Wire_3_5.FinalPass.ListEvalRef

/-! # S2 (THR per point), part 5: one occurrence of the population builder, both cases (P3:2596-2606)

`selB sgn d as X`: the population bits `Z^±` (`popG` of the four corners) of the occurrences whose coefficient has
digit `d` equal to `1`, in order (the digit population of `thrDigitPop` with `b₀ = 2`). One occurrence of the builder
(`occStep`: read `a_i`, its digit bit, the selection) appends its entry: **`occStep_sel`** (digit `1`: marker and bit
written, the population's counters step) and **`occStep_skip`** (digit `0`: the corners skipped).
Paper quantity: the digit population `thrDigitPop` (P3:2598-2599). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop

/-! ## The selected population -/

/-- **The selected population bits**: occurrence `i`'s `Z^±` when digit `d` of `a_i` is `1`. -/
def selB (sgn : Bool) (d : ℕ) : List ℕ → List Bool → List Bool
  | a :: as, b1 :: b2 :: b3 :: b4 :: X =>
      (if a / 2 ^ d % 2 = 1 then [popG sgn [b1, b2, b3, b4]] else []) ++ selB sgn d as X
  | _, _ => []

theorem selB_snoc (sgn : Bool) (d : ℕ) : ∀ (asP : List ℕ) (XP : List Bool) (a : ℕ) (bs : List Bool),
    XP.length = 4 * asP.length → bs.length = 4 →
    selB sgn d (asP ++ [a]) (XP ++ bs) = selB sgn d asP XP ++ (if a / 2 ^ d % 2 = 1 then [popG sgn bs] else [])
  | [], XP, a, bs, hX, hb => by
    obtain rfl : XP = [] := List.eq_nil_of_length_eq_zero (by simpa using hX)
    match bs, hb with
    | [b1, b2, b3, b4], _ => simp [selB]
  | a0 :: asP, b1 :: b2 :: b3 :: b4 :: XP, a, bs, hX, hb => by
    have hX' : XP.length = 4 * asP.length := by simp at hX; omega
    simp only [List.cons_append, selB, selB_snoc sgn d asP XP a bs hX' hb, List.append_assoc]
  | _ :: _, [], _, _, hX, _ => by simp only [List.length_cons, List.length_nil] at hX; omega
  | _ :: _, [_], _, _, hX, _ => by simp only [List.length_cons, List.length_nil] at hX; omega
  | _ :: _, [_, _], _, _, hX, _ => by simp only [List.length_cons, List.length_nil] at hX; omega
  | _ :: _, [_, _, _], _, _, hX, _ => by simp only [List.length_cons, List.length_nil] at hX; omega

theorem selB_length_le (sgn : Bool) (d : ℕ) : ∀ (as : List ℕ) (X : List Bool), (selB sgn d as X).length ≤ as.length
  | a :: as, b1 :: b2 :: b3 :: b4 :: X => by
    have := selB_length_le sgn d as X
    simp only [selB, List.length_append, List.length_cons]
    split_ifs <;> simp <;> omega
  | [], _ => by simp [selB]
  | _ :: _, [] => by simp [selB]
  | _ :: _, [_] => by simp [selB]
  | _ :: _, [_, _] => by simp [selB]
  | _ :: _, [_, _, _] => by simp [selB]

/-! ## Reading lemmas -/

theorem rd_drop (l : List Bool) (h k : ℕ) : readTapeBit l (h + k) = readTapeBit (l.drop h) k := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem rd_unary_lt (n k : ℕ) (rest : List Bool) (hk : k < n) :
    readTapeBit (ListEval.unary n ++ rest) k = true := by
  unfold readTapeBit ListEval.unary
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_left (by simpa using hk),
    List.getElem?_replicate]
  simp [hk]

theorem rd_unary_end (n : ℕ) (rest : List Bool) : readTapeBit (ListEval.unary n ++ rest) n = false := by
  unfold readTapeBit ListEval.unary
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by simp)]
  simp

variable (cap : ℕ)

/-! ## One occurrence -/

/-- One occurrence's step bound. -/
def occCost (A D : ℕ) : ℕ := 11 * A + 7 + 1 + (bitDCost A D + 1 + 90)

theorem bitDCost_mono (a A D : ℕ) (h : a ≤ A) : bitDCost a D ≤ bitDCost A D := by
  unfold bitDCost
  have := Nat.mul_le_mul_left D (show 12 * a + 7 ≤ 12 * A + 7 by omega)
  omega

theorem occStep_sel (sgn : Bool) (D a A0 : ℕ) (s : PSt) (restR XP bs restX sel zr : List Bool) (z0 z1 : Bool)
    (hrw : s.rw.drop s.rwh = ListEval.unary a ++ restR) (ha0 : a ≤ A0) (hbit : a / 2 ^ D % 2 = 1)
    (hl : bs.length = 4) (hX : s.x = frameP XP ++ frameP bs ++ restX) (hxh : s.xh = 2 * XP.length)
    (hZ : s.z = frameP sel ++ z0 :: z1 :: zr) (hzh : s.zh = 2 * sel.length)
    (hd : s.d = D) (ha : s.a = 0) (ht : s.t = 0) (he : s.e = 0) (hp : s.pb = 0) (hrem : 1 ≤ s.rem)
    (hcap : s.hr + A0 + 1 ≤ cap) (hA : 2 * A0 + 2 ≤ cap) (hD : 2 * D + 2 ≤ cap) (hcx : s.hx + 8 ≤ cap)
    (hcz : s.hz + 2 ≤ cap) (hcr : s.rem ≤ cap) :
    WExec cap (occStep sgn) s.w
      { s with rwh := s.rwh + a + 1, hr := s.hr + a + 1, z := frameP (sel ++ [popG sgn bs]) ++ zr,
               xh := s.xh + 8, zh := 2 * sel.length + 2, hx := s.hx + 8, hz := s.hz + 2, rem := s.rem - 1 }.w
      (occCost A0 D) := by
  have e1 := readA_spec cap s a (fun k hk => by rw [rd_drop, hrw]; exact rd_unary_lt a k restR hk)
    (by rw [rd_drop, hrw]; exact rd_unary_end a restR) (by omega) (by omega)
  have e2 := bitD_spec cap a D { s with rwh := s.rwh + a + 1, hr := s.hr + a + 1, a := s.a + a }
    (by simp only; omega) hd ht he hp (by omega) hD
  have e3 := selStep_one cap sgn
    { { s with rwh := s.rwh + a + 1, hr := s.hr + a + 1, a := s.a + a } with a := 0, pb := a / 2 ^ D % 2 }
    (frameP XP) (frameP sel) zr restX bs z0 z1 hl hX (by simp only; rw [hxh, fP_length]) hZ
    (by simp only; rw [hzh, fP_length]) (by simp only; exact hbit) hrem hcx hcz hcr (by omega)
  have hz' : frameP (sel ++ [popG sgn bs]) ++ zr = frameP sel ++ true :: popG sgn bs :: zr := by simp [frameP]
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) (w_eq ?_) ?_
  · rw [hz', fP_length]
    obtain ⟨⟩ := s
    simp only at ha hp ⊢
    pst_rec
  · unfold occCost
    have := bitDCost_mono a A0 D ha0
    omega

theorem occStep_skip (sgn : Bool) (D a A0 : ℕ) (s : PSt) (restR : List Bool)
    (hrw : s.rw.drop s.rwh = ListEval.unary a ++ restR) (ha0 : a ≤ A0) (hbit : a / 2 ^ D % 2 = 0)
    (hd : s.d = D) (ha : s.a = 0) (ht : s.t = 0) (he : s.e = 0) (hp : s.pb = 0)
    (hcap : s.hr + A0 + 1 ≤ cap) (hA : 2 * A0 + 2 ≤ cap) (hD : 2 * D + 2 ≤ cap) (hcx : s.hx + 8 ≤ cap) :
    WExec cap (occStep sgn) s.w
      { s with rwh := s.rwh + a + 1, hr := s.hr + a + 1, xh := s.xh + 8, hx := s.hx + 8 }.w (occCost A0 D) := by
  have e1 := readA_spec cap s a (fun k hk => by rw [rd_drop, hrw]; exact rd_unary_lt a k restR hk)
    (by rw [rd_drop, hrw]; exact rd_unary_end a restR) (by omega) (by omega)
  have e2 := bitD_spec cap a D { s with rwh := s.rwh + a + 1, hr := s.hr + a + 1, a := s.a + a }
    (by simp only; omega) hd ht he hp (by omega) hD
  have e3 := selStep_zero cap sgn
    { { s with rwh := s.rwh + a + 1, hr := s.hr + a + 1, a := s.a + a } with a := 0, pb := a / 2 ^ D % 2 }
    (by simp only; exact hbit) (by simp only; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) (w_eq ?_) ?_
  · obtain ⟨⟩ := s
    simp only at ha hp ⊢
    pst_rec
  · unfold occCost
    have := bitDCost_mono a A0 D ha0
    omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
