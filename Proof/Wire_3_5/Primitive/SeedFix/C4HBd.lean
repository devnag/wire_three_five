import Proof.Wire_3_5.Primitive.SeedFix.C4HBc

/-! # C4HB, part 4: one cell's cost and capacities at the data size

P3:2262-2268. At every cell `cc < n` of the Hb printer at the call's data (`DataOk D`, `plen ≤ 2tℓ₀`), with
`Q = hbS D + 1`: the term program's bound `tcB ≤ 160000·Q⁴`, the cell's cost `cellCost ≤ 400000·Q⁶`, and every
capacity the cell's programs need at most `10⁶·Q⁵`.

* `le_big`, `termBound_at`, `tcB_at`, `valBound_at`, `consBound_at`, `advB_at`, **`cellCost_at`**.

Paper quantity: none (the Hb printer's step counts). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord)

/-- A bound `C·Q^k` with `C ≤ 2^32`, `k ≤ 8` is below `2^32·Q^8`. -/
theorem le_big (r C k Q : ℕ) (h : r ≤ C * Q ^ k) (hC : C ≤ 2 ^ 32) (hk : k ≤ 8) (hQ : 1 ≤ Q) :
    r ≤ 2 ^ 32 * Q ^ 8 :=
  h.trans (Nat.mul_le_mul hC (Nat.pow_le_pow_right hQ hk))

section At
variable (D : HashData) (hD : DataOk D) (c : HbCaps) (plen pfx : ℕ)
include hD

theorem termBound_at (cc : ℕ) (hc : cc < (hbX D c plen pfx).n) :
    termBound (hbX D c plen pfx).Fs (hbX D c plen pfx).pops (hbX D c plen pfx).Ws
      ((hbX D c plen pfx).outAt cc).length (hbX D c plen pfx).T2 ((hbX D c plen pfx).lamOf cc) (hbX D c plen pfx).J
      ((hbX D c plen pfx).xOf cc) ((hbX D c plen pfx).eOf cc) ((hbX D c plen pfx).qOf cc) (hbX D c plen pfx).nE
      ((hbX D c plen pfx).idxOf cc) ((hbX D c plen pfx).pOf cc) (hbX D c plen pfx).G (hbX D c plen pfx).ℓ ≤
      140000 * (hbS D + 1) ^ 4 := by
  have hQ : 1 ≤ hbS D + 1 := by omega
  have hO := outAt_le D hD c plen pfx cc hc.le
  have hx : (hbX D c plen pfx).xOf cc ≤ hbS D + 1 := by have := (cell_x D c plen pfx cc).trans (hbS_Tl D); omega
  have hlam : (hbX D c plen pfx).lamOf cc ≤ hbS D + 1 := by
    have := (cell_lam D c plen pfx cc).trans (hbS_J D); omega
  have hwt : (wtWord (hbX D c plen pfx).Ws).length ≤ hbS D + 1 := by
    have : (wtWord (hbX D c plen pfx).Ws).length ≤ hbS D := hbS_wt D; omega
  have hfr : (frame ((hbX D c plen pfx).Ws.getD ((hbX D c plen pfx).lamOf cc) [])).length ≤ hbS D + 1 := by
    have hl : (hbX D c plen pfx).lamOf cc < (hbX D c plen pfx).Ws.length := by
      show (hbX D c plen pfx).lamOf cc < (wsOf D.MP).length
      simp only [wsOf, List.length_map, List.length_range]; have := cell_lam D c plen pfx cc; omega
    rw [List.getD_eq_getElem _ _ hl]
    have := frame_le_wt _ _ hl
    omega
  have hco := coefCost_le _ _ _ _ (hbS D + 1) hQ hx hlam hwt hfr
  have he : (hbX D c plen pfx).eOf cc ≤ hbS D + 1 := by have := cell_e D c plen pfx cc hc; have := hbS_nE D; omega
  have hq : (hbX D c plen pfx).qOf cc ≤ hbS D + 1 := by have := cell_q D c plen pfx cc hc; have := hbS_N2 D; omega
  have hnE : (hbX D c plen pfx).nE ≤ hbS D + 1 := by
    have : (hbX D c plen pfx).nE ≤ hbS D := hbS_nE D; omega
  have hidx : (hbX D c plen pfx).idxOf cc ≤ (hbS D + 1) ^ 2 := by
    have h1 := cell_idx D c plen pfx cc hc
    have h2 : D.N ^ 2 * D.nE ≤ (hbS D + 1) * (hbS D + 1) :=
      Nat.mul_le_mul (by have := hbS_N2 D; omega) (by have := hbS_nE D; omega)
    rw [sq]; omega
  have hht : (htWord (hbX D c plen pfx).Fs).length ≤ hbS D + 1 := by
    have : (htWord (hbX D c plen pfx).Fs).length ≤ hbS D := hbS_ht D; omega
  have hpl : (polyWord ((hbX D c plen pfx).Fs.getD ((hbX D c plen pfx).idxOf cc) [])).length ≤ hbS D + 1 :=
    (polyWord_le_ht _ _).trans hht
  have hfa := factorCost_le _ _ _ _ _ _ (hbS D + 1) hQ he hq hnE hidx hht hpl
  have hp : (hbX D c plen pfx).pOf cc ≤ hbS D + 1 := by have := cell_p D c plen pfx cc hc; have := hbS_P D; omega
  have hpw : (popsWord (hbX D c plen pfx).pops).length ≤ hbS D + 1 := by
    have : (popsWord (hbX D c plen pfx).pops).length ≤ hbS D := hbS_pw D; omega
  have hG : (hbX D c plen pfx).G ≤ hbS D + 1 := by
    have : (hbX D c plen pfx).G ≤ hbS D := hbS_G D; omega
  have hl : (hbX D c plen pfx).ℓ ≤ hbS D + 1 := by
    have : (hbX D c plen pfx).ℓ ≤ hbS D := hbS_l D; omega
  have hA : 2 ^ (hbX D c plen pfx).ℓ ≤ hbS D + 1 := by
    have : 2 ^ (hbX D c plen pfx).ℓ ≤ hbS D := hbS_l1 D; omega
  have hT2 : (hbX D c plen pfx).T2 ≤ hbS D + 1 := by
    have : (hbX D c plen pfx).T2 ≤ hbS D := hbS_T2 D; omega
  have hJ : (hbX D c plen pfx).J ≤ hbS D + 1 := by
    have : (hbX D c plen pfx).J ≤ hbS D := hbS_J D; omega
  have hz := zBodyBound_le ((hbX D c plen pfx).qOf cc) (hbX D c plen pfx).G (hbX D c plen pfx).ℓ
    ((hbX D c plen pfx).pOf cc) (popsWord (hbX D c plen pfx).pops).length (hbS D + 1) hQ hq hG hl hA hp hpw
  unfold termBound
  have m1 : (hbX D c plen pfx).pOf cc * (9 * (popsWord (hbX D c plen pfx).pops).length + 20 + 4) ≤
      (hbS D + 1) * (9 * (hbS D + 1) + 24) := Nat.mul_le_mul hp (by omega)
  have e1 : (hbS D + 1) * (9 * (hbS D + 1) + 24) = 9 * (hbS D + 1) ^ 2 + 24 * (hbS D + 1) := by ring
  have m2 : (hbX D c plen pfx).T2 * (zBodyBound ((hbX D c plen pfx).qOf cc) (hbX D c plen pfx).G
      (hbX D c plen pfx).ℓ ((hbX D c plen pfx).pOf cc) (popsWord (hbX D c plen pfx).pops).length + 4) ≤
      (hbS D + 1) * (130004 * (hbS D + 1) ^ 2) := Nat.mul_le_mul hT2 (by
        have := Nat.one_le_pow 2 (hbS D + 1) hQ; omega)
  have e2 : (hbS D + 1) * (130004 * (hbS D + 1) ^ 2) = 130004 * (hbS D + 1) ^ 3 := by ring
  have p12 := q_le_q2 (hbS D + 1)
  have p23 := q2_le_q3 (hbS D + 1) hQ
  have p34 : (hbS D + 1) ^ 3 ≤ (hbS D + 1) ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
  generalize (hbS D + 1) ^ 2 = Q2 at *
  generalize (hbS D + 1) ^ 3 = Q3 at *
  generalize (hbS D + 1) ^ 4 = Q4 at *
  omega

theorem tcB_at (cc : ℕ) (hc : cc < (hbX D c plen pfx).n) :
    (hbX D c plen pfx).tcB cc ≤ 160000 * (hbS D + 1) ^ 4 := by
  have hQ : 1 ≤ hbS D + 1 := by omega
  have ht := termBound_at D hD c plen pfx cc hc
  have hb := tb_le D hD c plen pfx cc hc
  have hq := cell_q D c plen pfx cc hc
  have he := cell_e D c plen pfx cc hc
  have hp := cell_p D c plen pfx cc hc
  have hlam := cell_lam D c plen pfx cc
  have h1 := hbS_N2 D
  have h2 : (hbX D c plen pfx).nE ≤ hbS D := hbS_nE D
  have h2' := hbS_nE D
  have h3 := hbS_P D
  have h4 : (hbX D c plen pfx).G ≤ hbS D := hbS_G D
  have h5 : (hbX D c plen pfx).J ≤ hbS D := hbS_J D
  have h5' := hbS_J D
  have h6 : (hbX D c plen pfx).T2 ≤ hbS D := hbS_T2 D
  have h7 : (hbX D c plen pfx).ℓ ≤ hbS D := hbS_l D
  unfold HbX.tcB ldSum
  have p34 : (hbS D + 1) ^ 3 ≤ (hbS D + 1) ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
  have p14 : hbS D + 1 ≤ (hbS D + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  generalize (hbS D + 1) ^ 3 = Q3 at *
  generalize (hbS D + 1) ^ 4 = Q4 at *
  omega

omit hD in
theorem valBound_at (cc : ℕ) (hc : cc < (hbX D c plen pfx).n) :
    valBound ((hbX D c plen pfx).lamOf cc) (hbX D c plen pfx).J ((hbX D c plen pfx).pOf cc) (hbX D c plen pfx).T2
      (hbX D c plen pfx).ℓ ((hbX D c plen pfx).popOf cc).2.length (popsWord (hbX D c plen pfx).pops).length ≤
      3000 * (hbS D + 1) ^ 3 := by
  refine valBound_le _ _ _ _ _ _ _ (hbS D + 1) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have := (cell_lam D c plen pfx cc).trans (hbS_J D); omega
  · have := hbS_J D; show D.MP.J ≤ _; omega
  · have := cell_p D c plen pfx cc hc; have := hbS_P D; omega
  · have := hbS_T2 D; show 2 * D.MP.t ≤ _; omega
  · have := hbS_l D; show D.MP.ell0 ≤ _; omega
  · have := hbS_l1 D; show 2 ^ D.MP.ell0 ≤ _; omega
  · have := (cell_pop D c plen pfx cc).trans (hbS_pw D); omega
  · have := hbS_pw D; show (popsWord D.pops).length ≤ _; omega

omit hD in
theorem consBound_at (cc : ℕ) :
    consBound ((hbX D c plen pfx).lamOf cc) (hbX D c plen pfx).J (hbX D c plen pfx).T2 (hbX D c plen pfx).ℓ ≤
      2000 * (hbS D + 1) ^ 2 := by
  refine consBound_le _ _ _ _ (hbS D + 1) (by omega) ?_ ?_ ?_ ?_
  · have := (cell_lam D c plen pfx cc).trans (hbS_J D); omega
  · have := hbS_J D; show D.MP.J ≤ _; omega
  · have := hbS_T2 D; show 2 * D.MP.t ≤ _; omega
  · have := hbS_l D; show D.MP.ell0 ≤ _; omega

omit hD in
theorem advB_at : (hbX D c plen pfx).advB ≤ 200 * (hbS D + 1) := by
  have := hbS_L D
  have := hbS_J D
  have := hbS_P D
  have := hbS_nE D
  have := hbS_N2 D
  show 7 * (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0) + 15 * (D.MP.J + 1 + D.pops.length + D.nE + D.N ^ 2) + 100 ≤ _
  omega

/-- **One cell's cost** at the data size. -/
theorem cellCost_at (cc : ℕ) (hc : cc < (hbX D c plen pfx).n) (hplen : plen ≤ 2 * D.MP.t * D.MP.ell0) :
    (hbX D c plen pfx).cellCost cc ≤ 400000 * (hbS D + 1) ^ 6 := by
  have hQ : 1 ≤ hbS D + 1 := by omega
  have hv := valBound_at D c plen pfx cc hc
  have hcs := consBound_at D c plen pfx cc
  have ht := tcB_at D hD c plen pfx cc hc
  have ha := advB_at D c plen pfx
  have hk : (hbX D c plen pfx).kOfC cc ≤ hbS D := (cell_k D c plen pfx cc).trans (hbS_J D)
  have he := PrimAsm.SFCost.elimCost_le' (hbX D c plen pfx).ℓ (hbX D c plen pfx).T2 ((hbX D c plen pfx).kOfC cc)
    (hbX D c plen pfx).plen (hbX D c plen pfx).T2 (hbS D) (hbS_l D) (hbS_T2 D) hk
    (show plen ≤ hbS D from hplen.trans (hbS_Tl D)) (hbS_T2 D)
  unfold HbX.cellCost
  have p23 := q2_le_q3 (hbS D + 1) hQ
  have p36 : (hbS D + 1) ^ 3 ≤ (hbS D + 1) ^ 6 := Nat.pow_le_pow_right hQ (by norm_num)
  have p46 : (hbS D + 1) ^ 4 ≤ (hbS D + 1) ^ 6 := Nat.pow_le_pow_right hQ (by norm_num)
  have p16 : hbS D + 1 ≤ (hbS D + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  generalize (hbS D + 1) ^ 2 = Q2 at *
  generalize (hbS D + 1) ^ 3 = Q3 at *
  generalize (hbS D + 1) ^ 4 = Q4 at *
  generalize (hbS D + 1) ^ 6 = Q6 at *
  omega

end At

end NearCubicWires.WireExponent3_5.PrimT.C4HB
