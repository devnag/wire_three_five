import Proof.Wire_3_5.FinalPass.SdEvC

/-! # S4 (the seeds phase), part 16: a seed's tables moved into place (P3:2036-2101, 3170-3178)

The seeds' tables are written once, as one word (`frame (table of carrier 0) ++ frame (table of carrier 1)` per seed,
then `0`); the seed loop moves each seed's two tables onto `tT 0`, `tT 1`. Every seed's table of carrier `k` has the
same length (`walkLen` visits of `128` coefficient words of length `L`), so a table is overwritten in place.
**`cpW`** (one framed word read at the source's head, written from `0` over a target of the same length; the source's
head past the word, the target's head back): **`cpW_spec`** on its own layout (`CpSt`), **`cpTB_spec`** on the body
(source `tTW` = stream `27` with its counter `rgT`, target `tT k`).

Paper quantity of the main type: the filter seed's tables `tableWord (filterTable FP e L)` in place for stage 7. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass

/-! ## The copy on its own layout -/

/-- The copy's record: source `a` and target `b`, their heads and counters, the cell. -/
structure CpSt where
  a : List Bool
  b : List Bool
  ha : ℕ
  hb : ℕ
  ca : ℕ
  cb : ℕ
  cell : Bool

/-- The word state of a record. -/
def CpSt.w (x : CpSt) : WState 1 2 := ⟨![x.ha, x.hb], ![x.a, x.b], ![x.ca, x.cb], x.cell⟩

theorem cpw_eq {x y : CpSt} (h : x = y) : x.w = y.w := congrArg CpSt.w h

variable (cap : ℕ)

theorem cp_fwdA (x : CpSt) (hc : x.ca < cap) : WExec cap (WM.fwdC 0 0) x.w { x with ha := x.ha + 1, ca := x.ca + 1 }.w 5 := by
  have e1 := WExec.fwd (cap := cap) (0 : Fin 2) x.w
  have e2 := WExec.inc (cap := cap) (0 : Fin 2) (x.w.seth 0 (x.w.sh 0 + 1)) hc
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply WState.eq <;> first | rfl | (funext i; fin_cases i <;> rfl)

theorem cp_fwdB (x : CpSt) (hc : x.cb < cap) : WExec cap (WM.fwdC 1 1) x.w { x with hb := x.hb + 1, cb := x.cb + 1 }.w 5 := by
  have e1 := WExec.fwd (cap := cap) (1 : Fin 2) x.w
  have e2 := WExec.inc (cap := cap) (1 : Fin 2) (x.w.seth 1 (x.w.sh 1 + 1)) hc
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply WState.eq <;> first | rfl | (funext i; fin_cases i <;> rfl)

theorem cp_wrB (x : CpSt) (v : Bool) : WExec cap (.wr 1 v) x.w { x with b := writeTapeBit x.b x.hb v }.w 1 := by
  have e := WExec.wr (cap := cap) (1 : Fin 2) v x.w
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq <;> first | rfl | (funext i; fin_cases i <;> rfl)

theorem cp_rewB (x : CpSt) (hc : x.cb ≤ cap) :
    WExec cap (WM.rewind 1 1) x.w { x with hb := x.hb - x.cb, cb := 0 }.w (5 * x.cb + 1) := by
  have e := wrewind_spec cap (1 : Fin 2) (1 : Fin 2) x.cb x.w rfl hc
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq <;> first | rfl | (funext i; fin_cases i <;> rfl)

/-- One bit: the source to its value, the value written on the target, both advanced. -/
def cpStep : WM 1 2 := .seq (WM.fwdC 0 0) (.seq (.ifs 0 (.wr 1 true) (.wr 1 false)) (.seq (WM.fwdC 0 0) (WM.fwdC 1 1)))

def cpLoop : WM 1 2 := .whs 0 cpStep

theorem cpLoop_spec (w w' rest : List Bool) (p : ℕ) (hw' : w'.length = w.length)
    (hcap : p + 2 * w.length + 1 < cap) :
    ∀ (m i : ℕ) (x : CpSt), w.length = i + m → x.a.drop p = frameP w ++ false :: rest → x.ha = p + 2 * i →
      x.ca = p + 2 * i → x.b = w.take i ++ w'.drop i → x.hb = i → x.cb = i →
      WExec cap cpLoop x.w
        { x with
          b := w, ha := p + 2 * w.length, ca := p + 2 * w.length, hb := w.length, cb := w.length }.w (m * 22 + 1)
  | 0, i, x, hl, ha, hh, hc, hb, hbh, hbc => by
    have hi : i = w.length := by omega
    have hr : wbit x.w 0 = false := by
      show readTapeBit x.a x.ha = false
      have e := ListEval.readTapeBit_drop x.a p (2 * i)
      rw [hh, e, ha, hi]
      exact readTapeBit_end w rest
    refine WExec.cast cap (WExec.whsF hr) (cpw_eq ?_) (by omega)
    obtain ⟨a, b, ha', hb', ca, cb, cell⟩ := x
    simp only at hb hh hc hbh hbc ⊢
    subst hb hh hc hbh hbc
    rw [hi, List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil]
  | m + 1, i, x, hl, ha, hh, hc, hb, hbh, hbc => by
    have hi : i < w.length := by omega
    have hr : wbit x.w 0 = true := by
      show readTapeBit x.a x.ha = true
      have e := ListEval.readTapeBit_drop x.a p (2 * i)
      rw [hh, e, ha]
      exact readTapeBit_frameP_marker w _ i hi
    have e1 := cp_fwdA cap x (by omega)
    obtain ⟨x1, hx1⟩ : ∃ y : CpSt, y = { x with ha := x.ha + 1, ca := x.ca + 1 } := ⟨_, rfl⟩
    rw [← hx1] at e1
    have hv : wbit x1.w 0 = w.getD i false := by
      show readTapeBit x1.a x1.ha = _
      rw [hx1]
      show readTapeBit x.a (x.ha + 1) = _
      have e := ListEval.readTapeBit_drop x.a p (2 * i + 1)
      rw [hh, show p + 2 * i + 1 = p + (2 * i + 1) by ring, e, ha]
      exact readTapeBit_frameP w _ i hi
    have e2 : WExec cap (.ifs 0 (.wr 1 true) (.wr 1 false)) x1.w
        { x1 with b := writeTapeBit x1.b x1.hb (w.getD i false) }.w 2 := by
      cases hg : w.getD i false
      · exact WExec.ifsF (by rw [hv, hg]) (cp_wrB cap x1 false)
      · exact WExec.ifsT (by rw [hv, hg]) (cp_wrB cap x1 true)
    obtain ⟨x2, hx2⟩ : ∃ y : CpSt, y = { x1 with b := writeTapeBit x1.b x1.hb (w.getD i false) } := ⟨_, rfl⟩
    rw [← hx2] at e2
    have e3 := cp_fwdA cap x2 (by rw [hx2, hx1]; show x.ca + 1 < cap; omega)
    obtain ⟨x3, hx3⟩ : ∃ y : CpSt, y = { x2 with ha := x2.ha + 1, ca := x2.ca + 1 } := ⟨_, rfl⟩
    rw [← hx3] at e3
    have e4 := cp_fwdB cap x3 (by rw [hx3, hx2, hx1]; show x.cb < cap; omega)
    have hbw : writeTapeBit x.b i (w.getD i false) = w.take (i + 1) ++ w'.drop (i + 1) := by
      have hd' : w'.drop i = w'.getD i false :: w'.drop (i + 1) := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.drop_eq_getElem_cons (by omega)
      have ht : (w.take i).length = i := by simp; omega
      have key := writeTapeBit_mid' (w.take i) (w'.drop (i + 1)) (w'.getD i false) (w.getD i false)
      rw [ht] at key
      rw [hb, hd', key, List.getD_eq_getElem _ _ hi, List.take_succ_eq_append_getElem hi, List.append_assoc]
      rfl
    have ih := cpLoop_spec w w' rest p hw' hcap m (i + 1) { x3 with hb := x3.hb + 1, cb := x3.cb + 1 } (by omega)
      (by rw [hx3, hx2, hx1]; exact ha) (by rw [hx3, hx2, hx1]; show x.ha + 1 + 1 = _; omega)
      (by rw [hx3, hx2, hx1]; show x.ca + 1 + 1 = _; omega)
      (by rw [hx3, hx2, hx1]; show writeTapeBit x.b (x.hb) (w.getD i false) = _; rw [hbh]; exact hbw)
      (by rw [hx3, hx2, hx1]; show x.hb + 1 = _; omega) (by rw [hx3, hx2, hx1]; show x.cb + 1 = _; omega)
    refine WExec.cast cap (WExec.whsT hr (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ih) (cpw_eq ?_)
      (by omega)
    rw [hx3, hx2, hx1]

/-- **The copy**: the loop, the source past the end mark, the target's head back. -/
def cpW : WM 1 2 := .seq cpLoop (.seq (WM.fwdC 0 0) (WM.rewind 1 1))

def cpCost (L : ℕ) : ℕ := L * 22 + 1 + 1 + (5 + 1 + (5 * L + 1))

theorem cpW_spec (w w' rest : List Bool) (p : ℕ) (hw' : w'.length = w.length) (hcap : p + 2 * w.length + 1 < cap)
    (x : CpSt) (ha : x.a.drop p = frameP w ++ false :: rest) (hh : x.ha = p) (hc : x.ca = p) (hb : x.b = w')
    (hbh : x.hb = 0) (hbc : x.cb = 0) :
    WExec cap cpW x.w { x with b := w, ha := p + 2 * w.length + 1, ca := p + 2 * w.length + 1 }.w (cpCost w.length) := by
  have e1 := cpLoop_spec cap w w' rest p hw' hcap w.length 0 x (by omega) ha (by omega) (by omega)
    (by rw [hb]; simp) hbh hbc
  obtain ⟨x1, hx1⟩ : ∃ y : CpSt, y =
      { x with
        b := w, ha := p + 2 * w.length, ca := p + 2 * w.length, hb := w.length, cb := w.length } := ⟨_, rfl⟩
  rw [← hx1] at e1
  have e2 := cp_fwdA cap x1 (by rw [hx1]; show p + 2 * w.length < cap; omega)
  have e3 := cp_rewB cap { x1 with ha := x1.ha + 1, ca := x1.ca + 1 } (by rw [hx1]; show w.length ≤ cap; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) (cpw_eq ?_) (by rw [hx1]; unfold cpCost; simp <;> omega)
  rw [hx1]
  obtain ⟨a, b, ha', hb', ca, cb, cell⟩ := x
  simp only at hbh hbc ⊢
  subst hbh hbc
  simp

/-! ## The copy on the body -/

section Lay
variable {nw nn nsc nrs : ℕ}

/-- The tables' word (stream `27`). -/
def tTW : Fin (bns nw nsc + 1) := bst 27 (by omega)

/-- The tables' word's counter and the target's counter. -/
def rgT : Fin (bnr nn nrs) := brg 200 (by omega)
def rgB : Fin (bnr nn nrs) := brg 201 (by omega)

def fsCp (k : Fin 2) (i : Fin 2) : Fin (bns nw nsc + 1) := bst (if i.val = 0 then 27 else 8 + k.val)
  (by have := k.isLt; split <;> omega)

def frCp (i : Fin 2) : Fin (bnr nn nrs) := brg (200 + i.val) (by have := i.isLt; omega)

theorem fsCp_inj (k : Fin 2) : Function.Injective (fsCp (nw := nw) (nsc := nsc) k) := by
  intro a b h
  have e := congrArg Fin.val h
  simp only [fsCp, bst] at e
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  have := k.isLt
  split_ifs at e <;> omega

theorem frCp_inj : Function.Injective (frCp (nn := nn) (nrs := nrs)) := fun a b h => Fin.ext (by
  have e := congrArg Fin.val h
  simp only [frCp, brg] at e
  omega)

theorem fsCp_0 (k : Fin 2) : fsCp (nw := nw) (nsc := nsc) k 0 = tTW := Fin.ext (by simp [fsCp, tTW, bst])
theorem fsCp_1 (k : Fin 2) : fsCp (nw := nw) (nsc := nsc) k 1 = tT k := Fin.ext (by simp [fsCp, tT, bst])
theorem frCp_0 : frCp (nn := nn) (nrs := nrs) 0 = rgT := Fin.ext (by simp [frCp, rgT, brg])
theorem frCp_1 : frCp (nn := nn) (nrs := nrs) 1 = rgB := Fin.ext (by simp [frCp, rgB, brg])

/-- **A table moved into place on the body.** -/
def cpTB (k : Fin 2) : BP nw nn nsc nrs := cpW.liftW (fsCp k) frCp

/-- The body after the move. -/
def cpOut (k : Fin 2) (w : List Bool) (p : ℕ) (ω : BS nw nn nsc nrs) : BS nw nn nsc nrs :=
  ((ω.sets (tT k) w).seth tTW p).setv rgT p

theorem cpTB_spec (cap : ℕ) (k : Fin 2) (w w' rest : List Bool) (p : ℕ) (ω : BS nw nn nsc nrs)
    (hw' : w'.length = w.length) (hcap : p + 2 * w.length + 1 < cap)
    (ha : (ω.st tTW).drop p = frameP w ++ false :: rest) (hh : ω.sh tTW = p) (hc : ω.val rgT = p)
    (hb : ω.st (tT k) = w') (hbh : ω.sh (tT k) = 0) (hbc : ω.val rgB = 0) :
    WExec cap (cpTB k) ω (cpOut k w (p + 2 * w.length + 1) ω) (cpCost w.length) := by
  have hTT : (tTW : Fin (bns nw nsc + 1)) ≠ tT k := by
    have := k.isLt; simp only [tTW, tT]; apply bst_ne; omega
  have hTB : (rgT : Fin (bnr nn nrs)) ≠ rgB := by simp only [rgT, rgB]; apply brg_ne; omega
  obtain ⟨x, hx⟩ : ∃ x : CpSt, x = ⟨ω.st tTW, ω.st (tT k), p, 0, p, 0, ω.cell⟩ := ⟨_, rfl⟩
  have hvw : viewW (fsCp k) frCp ω = x.w := by
    rw [hx]
    apply WState.eq
    · funext i; fin_cases i
      · show ω.sh (fsCp k 0) = p; rw [fsCp_0]; exact hh
      · show ω.sh (fsCp k 1) = 0; rw [fsCp_1]; exact hbh
    · funext i; fin_cases i
      · show ω.st (fsCp k 0) = ω.st tTW; rw [fsCp_0]
      · show ω.st (fsCp k 1) = ω.st (tT k); rw [fsCp_1]
    · funext q; fin_cases q
      · show ω.val (frCp 0) = p; rw [frCp_0]; exact hc
      · show ω.val (frCp 1) = 0; rw [frCp_1]; exact hbc
    · rfl
  have e := cpW_spec cap w w' rest p hw' hcap x (by rw [hx]; exact ha) (by rw [hx]) (by rw [hx]) (by rw [hx]; exact hb)
    (by rw [hx]) (by rw [hx])
  rw [← hvw] at e
  have e2 := ThrPt.WExec.liftW_upd cap (fsCp_inj k) frCp_inj e ω (liftW_view _ _ ω)
  refine WExec.cast cap e2 ?_ le_rfl
  apply WState.eq
  · funext j
    by_cases hj : ∃ i, fsCp k i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [ThrPt.updW_sh_in (fsCp_inj k)]
      fin_cases i
      · show p + 2 * w.length + 1 = (cpOut k w (p + 2 * w.length + 1) ω).sh (fsCp k 0)
        rw [fsCp_0]; simp [cpOut]
      · show x.hb = (cpOut k w (p + 2 * w.length + 1) ω).sh (fsCp k 1)
        rw [fsCp_1, hx]
        simp only [cpOut, WState.setv_sh, WState.seth_sh, WState.sets_sh]
        rw [Function.update_of_ne hTT.symm, hbh]
    · rw [ThrPt.updW_sh_out _ _ j (fun i h => hj ⟨i, h⟩)]
      have hne : j ≠ tTW := fun h => hj ⟨0, (fsCp_0 k).trans h.symm⟩
      simp only [cpOut, WState.setv_sh, WState.seth_sh, WState.sets_sh]
      rw [Function.update_of_ne hne]
  · funext j
    by_cases hj : ∃ i, fsCp k i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [ThrPt.updW_st_in (fsCp_inj k)]
      fin_cases i
      · show x.a = (cpOut k w (p + 2 * w.length + 1) ω).st (fsCp k 0)
        rw [fsCp_0, hx]
        simp only [cpOut, WState.setv_st, WState.seth_st, WState.sets_st]
        rw [Function.update_of_ne hTT]
      · show w = (cpOut k w (p + 2 * w.length + 1) ω).st (fsCp k 1)
        rw [fsCp_1]; simp [cpOut]
    · rw [ThrPt.updW_st_out _ _ j (fun i h => hj ⟨i, h⟩)]
      have hne : j ≠ tT k := fun h => hj ⟨1, (fsCp_1 k).trans h.symm⟩
      simp only [cpOut, WState.setv_st, WState.seth_st, WState.sets_st]
      rw [Function.update_of_ne hne]
  · funext q
    by_cases hq : ∃ r, frCp r = q
    · obtain ⟨r, rfl⟩ := hq
      rw [ThrPt.updW_val_in frCp_inj]
      fin_cases r
      · show p + 2 * w.length + 1 = (cpOut k w (p + 2 * w.length + 1) ω).val (frCp 0)
        rw [frCp_0]; simp [cpOut]
      · show x.cb = (cpOut k w (p + 2 * w.length + 1) ω).val (frCp 1)
        rw [frCp_1, hx]
        simp only [cpOut, WState.setv_val, WState.seth_val, WState.sets_val]
        rw [Function.update_of_ne hTB.symm, hbc]
    · rw [ThrPt.updW_val_out _ _ q (fun r h => hq ⟨r, h⟩)]
      have hne : q ≠ rgT := fun h => hq ⟨0, frCp_0.trans h.symm⟩
      simp only [cpOut, WState.setv_val, WState.seth_val, WState.sets_val]
      rw [Function.update_of_ne hne]
  · rw [ThrPt.updW_cell, hx]
    rfl

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.Sd
