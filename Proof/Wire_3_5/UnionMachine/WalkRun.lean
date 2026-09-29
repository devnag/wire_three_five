import Proof.Wire_3_5.UnionMachine.WalkKit
import Proof.Wire_3_5.UnionMachine.WalkMath

/-! # C6 tail, item 3 (part 3): the walk bank's word program pieces

On the walk-bank producer's ports as streams (`0 … 7` the bank, `8` the counter, `9` the framed index word, `10 … 13`
the rulers `1^r, 1^n, 1^R, 1^LW`; register `0` counts the rulers):
* **`lab_spec`**: the labels' word, unframed from the index word's first `160n` pairs onto port `7`;
* **`cnt_spec`**: the counter word `CompareMachine.word n = F 1^n` on port `8`;
* **`pad_spec`**: a coordinate word `pad R (frame w)` from the index word's next `|w|` pairs (the `R` ruler padding).

Paper quantity of the main types: the walk sample's edge labels and start coordinates in the bank. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.WalkRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emitW)
open NearCubicWires.WireExponent3_5.UnionMachine.TailAsm (Cp Cp.refl Cp.tr cp_emit rbW fp_cons fp_app fpl)
open NearCubicWires.WireExponent3_5.UnionMachine.SampKit
open NearCubicWires.WireExponent3_5.UnionMachine.WalkKit

variable (cap : ℕ)

/-! ## The labels -/

/-- The labels' word: per cell of the ruler `1^n`, `160` bits unframed from the index word onto port `7`. -/
def labW : WM 13 1 := rulerW 11 0 (repG (.seq (.fwd 9) (rbW 9 7)) 160)

theorem lab_spec (lw rest : List Bool) (n : ℕ) (hlw : lw.length = 160 * n) (hn : n ≤ cap) (σ : WState 13 1)
    (hX : σ.st 9 = frameP lw ++ rest) (hhX : σ.sh 9 = 0) (hD : σ.sh 7 = (σ.st 7).length)
    (hR : σ.st 11 = List.replicate n true) (hh : σ.sh 11 = 0) (hc : σ.val 0 = 0) :
    ∃ τ, WExec cap labW σ τ (n * (160 * 9 + 13) + 3) ∧ Cp 9 7 σ τ (frameP lw) lw := by
  have hB : ∀ k, k < n → ∀ σ' : WState 13 1,
      Cp 9 7 σ (nrm 11 0 σ') (frameP (lw.take (160 * k))) (lw.take (160 * k)) →
      σ'.st 11 = List.replicate n true → σ'.sh 11 = k → σ'.val 0 = k →
      ∃ τ, WExec cap (repG (.seq (.fwd 9) (rbW 9 7)) 160) σ' τ (160 * 9) ∧
        Cp 9 7 σ (nrm 11 0 τ) (frameP (lw.take (160 * (k + 1)))) (lw.take (160 * (k + 1))) ∧
        τ.st 11 = σ'.st 11 ∧ τ.sh 11 = σ'.sh 11 ∧ τ.val 0 = σ'.val 0 := by
    intro k hk σ' hP' _ _ _
    have hck : ((lw.drop (160 * k)).take 160).length = 160 := by
      rw [List.length_take, List.length_drop, hlw]
      have : 160 * k + 160 ≤ 160 * n := by omega
      omega
    have hsplit : lw.take (160 * (k + 1)) = lw.take (160 * k) ++ (lw.drop (160 * k)).take 160 := by
      rw [show 160 * (k + 1) = 160 * k + 160 by ring, List.take_add]
    have hX' : σ'.st 9 = frameP (lw.take (160 * k)) ++ (frameP ((lw.drop (160 * k)).take 160) ++
        (frameP ((lw.drop (160 * k)).drop 160) ++ rest)) := by
      rw [show σ'.st 9 = σ.st 9 from hP'.st, hX]
      conv_lhs => rw [← List.take_append_drop (160 * k) lw, ← List.take_append_drop 160 (lw.drop (160 * k))]
      simp only [fp_app, List.append_assoc]
    have hhX' : σ'.sh 9 = (frameP (lw.take (160 * k))).length := by
      have := hP'.sh
      simp only [nrm, WState.setv_sh, WState.seth_sh,
        Function.update_of_ne (show (9 : Fin 14) ≠ 11 by decide)] at this
      rw [this, hhX, Nat.zero_add]
    have hD' : σ'.sh 7 = (σ'.st 7).length := by
      have := hP'.endO
      simp only [nrm, WState.setv_sh, WState.seth_sh, WState.setv_st, WState.seth_st,
        Function.update_of_ne (show (7 : Fin 14) ≠ 11 by decide)] at this
      exact this
    obtain ⟨τ, s, c1⟩ := unf_spec cap 9 7 (by decide) ((lw.drop (160 * k)).take 160) _ _ σ' hX' hhX' hD'
    rw [hck] at s
    refine ⟨τ, s, hP'.tr (cp_nrm 11 9 7 0 (by decide) (by decide) c1) (by rw [hsplit, fp_app]) (by rw [hsplit]),
      ?_, ?_, ?_⟩
    · exact (c1.same 11 (by decide) (by decide)).1
    · exact (c1.same 11 (by decide) (by decide)).2
    · rw [c1.val]
  obtain ⟨τ, s, hP, -, -, -⟩ := ruler_spec cap 11 0 (repG (.seq (.fwd 9) (rbW 9 7)) 160) n (160 * 9)
    (fun k τ => Cp 9 7 σ τ (frameP (lw.take (160 * k))) (lw.take (160 * k))) hn hB σ
    (by simpa using Cp.refl 9 7 σ hD) hR hh hc
  rw [show 160 * n = lw.length from hlw.symm, List.take_length] at hP
  exact ⟨τ, s, hP⟩

/-! ## The counter word -/

/-- The counter word `F 1^n` on port `8`. -/
def cntW : WM 13 1 := .seq (emitW 8 false) (rulerW 11 0 (emitW 8 true))

theorem cnt_spec (n : ℕ) (hn : n ≤ cap) (σ : WState 13 1) (hD : σ.st 8 = []) (hhD : σ.sh 8 = 0)
    (hR : σ.st 11 = List.replicate n true) (hh : σ.sh 11 = 0) (hc : σ.val 0 = 0) :
    ∃ τ, WExec cap cntW σ τ (3 + 1 + (n * 16 + 3)) ∧ Cp 9 8 σ τ [] (false :: List.replicate n true) := by
  obtain ⟨τ1, s1, c1⟩ := cp_emit cap 9 8 (by decide) false σ (by simp [hD, hhD])
  obtain ⟨τ, s2, c2⟩ := fillP_spec cap 11 9 8 0 (by decide) (by decide) (by decide) true n hn τ1 c1.endO
    (by rw [(c1.same 11 (by decide) (by decide)).1]; exact hR) (by rw [(c1.same 11 (by decide) (by decide)).2]; exact hh)
    (by rw [c1.val]; exact hc)
  exact ⟨τ, WExec.seq s1 s2, c1.tr c2 rfl rfl⟩

/-! ## A padded coordinate word -/

/-- A coordinate word `pad R (frame w)` on the blank port `D`: the next `|w|` pairs of the index word (ruler `1^r`), its
end mark, the `R` ruler's head moved past `2|w| + 1` cells, zeros to its end, and the `R` ruler returned. -/
def padW (D : Fin 14) : WM 13 1 :=
  .seq (rulerW 10 0 (.seq (rbW 9 D) (rbW 9 D))) (.seq (emitW D false)
    (.seq (rulerW 10 0 (.seq (.fwd 12) (.fwd 12))) (.seq (.fwd 12)
    (.seq (.whs 12 (.seq (emitW D false) (.seq (.fwd 12) (.inc 0))))
    (.seq (WM.rewind 12 0) (.seq (rulerW 10 0 (.seq (.bwd 12) (.bwd 12))) (.bwd 12)))))))

def padCost (r R : ℕ) : ℕ :=
  r * 26 + 3 + 1 + (3 + 1 + (r * 16 + 3 + 1 + (1 + 1 + ((R - (2 * r + 1)) * 11 + 1 + 1 +
    (5 * (R - (2 * r + 1)) + 1 + 1 + (r * 16 + 3 + 1 + 1))))))

theorem pad_spec (D : Fin 14) (h9 : D ≠ 9) (h10 : D ≠ 10) (h12 : D ≠ 12) (w pre rest : List Bool) (R : ℕ)
    (hR2 : 2 * w.length + 1 ≤ R) (hRc : R ≤ cap) (σ : WState 13 1)
    (hX : σ.st 9 = pre ++ (frameP w ++ rest)) (hhX : σ.sh 9 = pre.length) (hD : σ.st D = []) (hhD : σ.sh D = 0)
    (hr : σ.st 10 = List.replicate w.length true) (hhr : σ.sh 10 = 0) (hRR : σ.st 12 = List.replicate R true)
    (hhR : σ.sh 12 = 0) (hc : σ.val 0 = 0) :
    ∃ τ, WExec cap (padW D) σ τ (padCost w.length R) ∧ τ.st D = ZeroPadding.pad R (frame w) ∧
      τ.st 9 = σ.st 9 ∧ τ.sh 9 = pre.length + 2 * w.length ∧ τ.st 10 = σ.st 10 ∧ τ.sh 10 = 0 ∧
      τ.st 12 = σ.st 12 ∧ τ.sh 12 = 0 ∧ τ.val 0 = 0 ∧
      (∀ j : Fin 14, j ≠ D → j ≠ 9 → j ≠ 10 → j ≠ 12 → Same σ τ j) ∧ τ.cell = σ.cell := by
  have hw : w.length ≤ cap := by omega
  obtain ⟨τ1, s1, c1⟩ := copyP_spec cap 10 9 D 0 (by decide) h10 (Ne.symm h9) w pre rest hw σ hX hhX
    (by simp [hD, hhD]) hr hhr hc
  obtain ⟨τ2, s2, c2⟩ := cp_emit cap 9 D (Ne.symm h9) false τ1 c1.endO
  have c12 := c1.tr c2 rfl rfl
  have g10 := c12.same 10 (by decide) (Ne.symm h10)
  have g12 := c12.same 12 (by decide) (Ne.symm h12)
  have hc2 : τ2.val 0 = 0 := by rw [c12.val]; exact hc
  have s3 := skipP_spec cap 10 12 0 (by decide) w.length hw τ2 (by rw [g10.1]; exact hr) (by rw [g10.2]; exact hhr)
    hc2
  have s4 := WExec.fwd (cap := cap) 12 (τ2.seth 12 (τ2.sh 12 + 2 * w.length))
  obtain ⟨τ5, s5, e5, eh5, f5, fh5, v5, o5, r5, cl5⟩ := padLoop_spec cap 12 D 0 h12 R hRc (R - (2 * w.length + 1)) 0
    ((τ2.seth 12 (τ2.sh 12 + 2 * w.length)).seth 12 ((τ2.seth 12 (τ2.sh 12 + 2 * w.length)).sh 12 + 1))
    (by simp only [WState.seth_sh, Function.update_self]; rw [g12.2, hhR]; omega) (by omega)
    (by simp only [WState.seth_st]; rw [g12.1, hRR]) (by simp only [WState.seth_val]; exact hc2)
    (by simp only [WState.seth_sh, WState.seth_st, Function.update_of_ne h12]; exact c12.endO)
    (by simp only [WState.seth_sh, Function.update_self]; rw [g12.2, hhR]; omega)
  have s6 := wrewind_spec cap 12 0 (R - (2 * w.length + 1)) τ5 (by rw [v5]; omega) (by rw [v5]; omega)
  have hL6 : ((τ5.setv 0 0).seth 12 (τ5.sh 12 - (R - (2 * w.length + 1)))).st 10 = List.replicate w.length true := by
    simp only [WState.seth_st, WState.setv_st]
    rw [(o5 10 (Ne.symm h10) (by decide)).1]; simp only [WState.seth_st]; rw [g10.1]; exact hr
  have hhL6 : ((τ5.setv 0 0).seth 12 (τ5.sh 12 - (R - (2 * w.length + 1)))).sh 10 = 0 := by
    simp only [WState.seth_sh, WState.setv_sh, Function.update_of_ne (show (10 : Fin 14) ≠ 12 by decide)]
    rw [(o5 10 (Ne.symm h10) (by decide)).2]
    simp only [WState.seth_sh, Function.update_of_ne (show (10 : Fin 14) ≠ 12 by decide)]
    rw [g10.2]; exact hhr
  have s7 := backP_spec cap 10 12 0 (by decide) w.length hw
    ((τ5.setv 0 0).seth 12 (τ5.sh 12 - (R - (2 * w.length + 1)))) hL6 hhL6 (by simp)
  have s8 := WExec.bwd (cap := cap) 12 (((τ5.setv 0 0).seth 12 (τ5.sh 12 - (R - (2 * w.length + 1)))).seth 12
    (((τ5.setv 0 0).seth 12 (τ5.sh 12 - (R - (2 * w.length + 1)))).sh 12 - 2 * w.length))
  refine ⟨_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 s8)))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hjD hj9 hj10 hj12 => ?_, ?_⟩
  · simp only [WState.seth_st, WState.setv_st]
    rw [e5]; simp only [WState.seth_st]; rw [c12.out, hD]
    simp only [ZeroPadding.pad, frame_eq_frameP, List.nil_append, List.append_assoc, List.length_append, fpl,
      List.length_singleton]
    try (congr 3 <;> omega)
  · simp only [WState.seth_st, WState.setv_st]
    rw [(o5 9 (Ne.symm h9) (by decide)).1]; simp only [WState.seth_st]; exact c12.st
  · simp only [WState.seth_sh, WState.setv_sh, Function.update_of_ne (show (9 : Fin 14) ≠ 12 by decide)]
    rw [(o5 9 (Ne.symm h9) (by decide)).2]
    simp only [WState.seth_sh, Function.update_of_ne (show (9 : Fin 14) ≠ 12 by decide)]
    rw [c12.sh, hhX]; simp [fpl]
  · simp only [WState.seth_st, WState.setv_st]
    rw [(o5 10 (Ne.symm h10) (by decide)).1]; simp only [WState.seth_st]; exact g10.1
  · simp only [WState.seth_sh, WState.setv_sh, Function.update_of_ne (show (10 : Fin 14) ≠ 12 by decide)]
    rw [(o5 10 (Ne.symm h10) (by decide)).2]
    simp only [WState.seth_sh, Function.update_of_ne (show (10 : Fin 14) ≠ 12 by decide)]
    rw [g10.2]; exact hhr
  · simp only [WState.seth_st, WState.setv_st]
    rw [f5]; simp only [WState.seth_st]; exact g12.1
  · simp only [WState.seth_sh, WState.setv_sh, Function.update_self]
    rw [fh5]; omega
  · simp
  · have e1 := c12.same j hj9 hjD
    have e2 := o5 j hjD hj12
    refine ⟨?_, ?_⟩
    · simp only [WState.seth_st, WState.setv_st]; rw [e2.1]; simp only [WState.seth_st]; exact e1.1
    · simp only [WState.seth_sh, WState.setv_sh, Function.update_of_ne hj12]
      rw [e2.2]; simp only [WState.seth_sh, Function.update_of_ne hj12]; exact e1.2
  · simp only [WState.seth_cell, WState.setv_cell]; rw [cl5]; simp only [WState.seth_cell]; exact c12.cell

/-! ## The work tapes -/

theorem only_of_cp {Y D : Fin 14} {σ τ : WState 13 1} {v : List Bool} (h : Cp Y D σ τ [] v) (j : Fin 14)
    (hj : j ≠ D) : Same σ τ j := by
  by_cases hY : j = Y
  · subst hY; exact ⟨h.st, by rw [h.sh]; rfl⟩
  · exact h.same j hY hj

/-- The work tapes `0^R`, `0^{LW}`, `1^R`, `0 1^R 0`, `0^{R+1}` on ports `2 … 6`. -/
def tapesW : WM 13 1 :=
  .seq (rulerW 12 0 (emitW 2 false)) (.seq (rulerW 13 0 (emitW 3 false)) (.seq (rulerW 12 0 (emitW 4 true))
    (.seq (.seq (emitW 5 false) (.seq (rulerW 12 0 (emitW 5 true)) (emitW 5 false)))
    (.seq (rulerW 12 0 (emitW 6 false)) (emitW 6 false)))))

def tapesCost (R LW : ℕ) : ℕ :=
  R * 16 + 3 + 1 + (LW * 16 + 3 + 1 + (R * 16 + 3 + 1 + (3 + 1 + (R * 16 + 3 + 1 + 3) + 1 + (R * 16 + 3 + 1 + 3))))

theorem tapes_spec (R LW : ℕ) (hR : R ≤ cap) (hL : LW ≤ cap) (σ : WState 13 1)
    (h2 : σ.st 2 = []) (hh2 : σ.sh 2 = 0) (h3 : σ.st 3 = []) (hh3 : σ.sh 3 = 0) (h4 : σ.st 4 = [])
    (hh4 : σ.sh 4 = 0) (h5 : σ.st 5 = []) (hh5 : σ.sh 5 = 0) (h6 : σ.st 6 = []) (hh6 : σ.sh 6 = 0)
    (hRR : σ.st 12 = List.replicate R true) (hhR : σ.sh 12 = 0) (hLL : σ.st 13 = List.replicate LW true)
    (hhL : σ.sh 13 = 0) (hc : σ.val 0 = 0) :
    ∃ τ, WExec cap tapesW σ τ (tapesCost R LW) ∧ τ.st 2 = List.replicate R false ∧
      τ.st 3 = List.replicate LW false ∧ τ.st 4 = List.replicate R true ∧ τ.st 5 = UnaryTemplate.tape R ∧
      τ.st 6 = List.replicate (R + 1) false ∧
      (∀ j : Fin 14, j ≠ 2 → j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 6 → Same σ τ j) ∧ τ.val 0 = 0 ∧ τ.cell = σ.cell := by
  obtain ⟨τa, sa, ca⟩ := fillP_spec cap 12 9 2 0 (by decide) (by decide) (by decide) false R hR σ
    (by simp [h2, hh2]) hRR hhR hc
  have ga := only_of_cp ca
  obtain ⟨τb, sb, cb⟩ := fillP_spec cap 13 9 3 0 (by decide) (by decide) (by decide) false LW hL τa
    (by rw [(ga 3 (by decide)).1, (ga 3 (by decide)).2, h3, hh3]; rfl)
    (by rw [(ga 13 (by decide)).1]; exact hLL) (by rw [(ga 13 (by decide)).2]; exact hhL) (by rw [ca.val]; exact hc)
  have gb := only_of_cp cb
  obtain ⟨τc, sc, cc⟩ := fillP_spec cap 12 9 4 0 (by decide) (by decide) (by decide) true R hR τb
    (by rw [(gb 4 (by decide)).1, (gb 4 (by decide)).2, (ga 4 (by decide)).1, (ga 4 (by decide)).2, h4, hh4]; rfl)
    (by rw [(gb 12 (by decide)).1, (ga 12 (by decide)).1]; exact hRR)
    (by rw [(gb 12 (by decide)).2, (ga 12 (by decide)).2]; exact hhR) (by rw [cb.val, ca.val]; exact hc)
  have gc := only_of_cp cc
  obtain ⟨τd1, sd1, cd1⟩ := cp_emit cap 9 5 (by decide) false τc
    (by rw [(gc 5 (by decide)).1, (gc 5 (by decide)).2, (gb 5 (by decide)).1, (gb 5 (by decide)).2,
      (ga 5 (by decide)).1, (ga 5 (by decide)).2, h5, hh5]; rfl)
  have gd1 := only_of_cp cd1
  obtain ⟨τd2, sd2, cd2⟩ := fillP_spec cap 12 9 5 0 (by decide) (by decide) (by decide) true R hR τd1 cd1.endO
    (by rw [(gd1 12 (by decide)).1, (gc 12 (by decide)).1, (gb 12 (by decide)).1, (ga 12 (by decide)).1]; exact hRR)
    (by rw [(gd1 12 (by decide)).2, (gc 12 (by decide)).2, (gb 12 (by decide)).2, (ga 12 (by decide)).2]; exact hhR)
    (by rw [cd1.val, cc.val, cb.val, ca.val]; exact hc)
  have gd2 := only_of_cp cd2
  obtain ⟨τd3, sd3, cd3⟩ := cp_emit cap 9 5 (by decide) false τd2 cd2.endO
  have gd3 := only_of_cp cd3
  obtain ⟨τe1, se1, ce1⟩ := fillP_spec cap 12 9 6 0 (by decide) (by decide) (by decide) false R hR τd3
    (by rw [(gd3 6 (by decide)).1, (gd3 6 (by decide)).2, (gd2 6 (by decide)).1, (gd2 6 (by decide)).2,
      (gd1 6 (by decide)).1, (gd1 6 (by decide)).2, (gc 6 (by decide)).1, (gc 6 (by decide)).2,
      (gb 6 (by decide)).1, (gb 6 (by decide)).2, (ga 6 (by decide)).1, (ga 6 (by decide)).2, h6, hh6]; rfl)
    (by rw [(gd3 12 (by decide)).1, (gd2 12 (by decide)).1, (gd1 12 (by decide)).1, (gc 12 (by decide)).1,
      (gb 12 (by decide)).1, (ga 12 (by decide)).1]; exact hRR)
    (by rw [(gd3 12 (by decide)).2, (gd2 12 (by decide)).2, (gd1 12 (by decide)).2, (gc 12 (by decide)).2,
      (gb 12 (by decide)).2, (ga 12 (by decide)).2]; exact hhR)
    (by rw [cd3.val, cd2.val, cd1.val, cc.val, cb.val, ca.val]; exact hc)
  have ge1 := only_of_cp ce1
  obtain ⟨τ, se2, ce2⟩ := cp_emit cap 9 6 (by decide) false τe1 ce1.endO
  have ge2 := only_of_cp ce2
  refine ⟨τ, WExec.seq sa (WExec.seq sb (WExec.seq sc (WExec.seq (WExec.seq sd1 (WExec.seq sd2 sd3))
    (WExec.seq se1 se2)))), ?_, ?_, ?_, ?_, ?_, fun j j2 j3 j4 j5 j6 => ?_, ?_, ?_⟩
  · rw [(ge2 2 (by decide)).1, (ge1 2 (by decide)).1, (gd3 2 (by decide)).1, (gd2 2 (by decide)).1,
      (gd1 2 (by decide)).1, (gc 2 (by decide)).1, (gb 2 (by decide)).1, ca.out, h2]; rfl
  · rw [(ge2 3 (by decide)).1, (ge1 3 (by decide)).1, (gd3 3 (by decide)).1, (gd2 3 (by decide)).1,
      (gd1 3 (by decide)).1, (gc 3 (by decide)).1, cb.out, (ga 3 (by decide)).1, h3]; rfl
  · rw [(ge2 4 (by decide)).1, (ge1 4 (by decide)).1, (gd3 4 (by decide)).1, (gd2 4 (by decide)).1,
      (gd1 4 (by decide)).1, cc.out, (gb 4 (by decide)).1, (ga 4 (by decide)).1, h4]; rfl
  · rw [(ge2 5 (by decide)).1, (ge1 5 (by decide)).1, cd3.out, cd2.out, cd1.out, (gc 5 (by decide)).1,
      (gb 5 (by decide)).1, (ga 5 (by decide)).1, h5]
    simp [UnaryTemplate.tape]
  · rw [ce2.out, ce1.out, (gd3 6 (by decide)).1, (gd2 6 (by decide)).1, (gd1 6 (by decide)).1,
      (gc 6 (by decide)).1, (gb 6 (by decide)).1, (ga 6 (by decide)).1, h6]
    rw [List.replicate_succ']; simp
  · exact (((((((ga j j2).trans' (gb j j3)).trans' (gc j j4)).trans' (gd1 j j5)).trans' (gd2 j j5)).trans'
      (gd3 j j5)).trans' (ge1 j j6)).trans' (ge2 j j6)
  · rw [ce2.val, ce1.val, cd3.val, cd2.val, cd1.val, cc.val, cb.val, ca.val]; exact hc
  · rw [ce2.cell, ce1.cell, cd3.cell, cd2.cell, cd1.cell, cc.cell, cb.cell, ca.cell]

/-! ## The bank -/

/-- **The walk bank's word program**: labels, counter word, the two coordinate words, the work tapes. -/
def bankW : WM 13 1 := .seq labW (.seq cntW (.seq (padW 1) (.seq (padW 0) tapesW)))

/-- The bank program's entry state: the framed index word and the rulers; every other stream blank. -/
def σB (r n R LW : ℕ) (w : List Bool) : WState 13 1 :=
  ⟨fun _ => 0, fun i => if i.val = 9 then frame w else if i.val = 10 then List.replicate r true
    else if i.val = 11 then List.replicate n true else if i.val = 12 then List.replicate R true
    else if i.val = 13 then List.replicate LW true else [], fun _ => 0, false⟩

def bankCost (r n R LW : ℕ) : ℕ :=
  n * (160 * 9 + 13) + 3 + 1 + (3 + 1 + (n * 16 + 3) + 1 + (padCost r R + 1 + (padCost r R + 1 + tapesCost R LW)))

theorem σB_blank (r n R LW : ℕ) (w : List Bool) (i : Fin 14) (hi : i.val < 9) : (σB r n R LW w).st i = [] := by
  simp only [σB]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **The walk bank**: from the framed index word and the rulers, the bank of `WalkTimeLoop.run`'s entry (ports
`0 … 7`), the counter word (port `8`), the inputs kept. -/
theorem bank_spec (r n R LW : ℕ) (sample : SupplierWalk.MargulisWalkSample (2 ^ r) (n + 1)) (hR : 2 * r + 1 ≤ R)
    (hc1 : n ≤ cap) (hc2 : R ≤ cap) (hc3 : LW ≤ cap) :
    ∃ τ, WExec cap bankW (σB r n R LW (PrimT.WalkBank.seedIndexWord r n sample)) τ (bankCost r n R LW) ∧
      τ.st 0 = ZeroPadding.pad R (frame (SignedSortKey.binary r sample.start.1.val)) ∧
      τ.st 1 = ZeroPadding.pad R (frame (SignedSortKey.binary r sample.start.2.val)) ∧
      τ.st 2 = List.replicate R false ∧ τ.st 3 = List.replicate LW false ∧ τ.st 4 = List.replicate R true ∧
      τ.st 5 = UnaryTemplate.tape R ∧ τ.st 6 = List.replicate (R + 1) false ∧
      τ.st 7 = Theorem25Completion.WalkSampleWord.labelsWord (SupplierWalk.sampleTransitionLabels sample) ∧
      τ.st 8 = false :: List.replicate n true ∧
      τ.st 9 = frame (PrimT.WalkBank.seedIndexWord r n sample) ∧ τ.st 10 = List.replicate r true ∧
      τ.st 11 = List.replicate n true ∧ τ.st 12 = List.replicate R true ∧ τ.st 13 = List.replicate LW true ∧
      τ.val 0 = 0 ∧ τ.cell = false := by
  set lw := Theorem25Completion.WalkSampleWord.labelsWord (SupplierWalk.sampleTransitionLabels sample) with hlwd
  set b2 := SignedSortKey.binary r sample.start.2.val with hb2
  set b1 := SignedSortKey.binary r sample.start.1.val with hb1
  have hlw : lw.length = 160 * n := Theorem25Completion.WalkSampleWord.labels_length _
  have hl2 : b2.length = r := SignedSortKey.binary_length _ _
  have hl1 : b1.length = r := SignedSortKey.binary_length _ _
  have hw : frame (PrimT.WalkBank.seedIndexWord r n sample) =
      frameP lw ++ (frameP b2 ++ (frameP b1 ++ [false])) := by
    rw [WalkMath.index_word, WalkMath.vtxWord, frame_eq_frameP, fp_app, fp_app]
    simp only [List.append_assoc]
    rfl
  set σ := σB r n R LW (PrimT.WalkBank.seedIndexWord r n sample) with hσ
  have h9 : σ.st 9 = frame (PrimT.WalkBank.seedIndexWord r n sample) := rfl
  have h10 : σ.st 10 = List.replicate r true := rfl
  have h11 : σ.st 11 = List.replicate n true := rfl
  have h12 : σ.st 12 = List.replicate R true := rfl
  have h13 : σ.st 13 = List.replicate LW true := rfl
  have hsh : ∀ i, σ.sh i = 0 := fun _ => rfl
  have hbl : ∀ i : Fin 14, i.val < 9 → σ.st i = [] := fun i hi => σB_blank r n R LW _ i hi
  -- the labels
  obtain ⟨τ1, s1, c1⟩ := lab_spec cap lw (frameP b2 ++ (frameP b1 ++ [false])) n hlw hc1 σ (by rw [h9, hw])
    (hsh 9) (by rw [hbl 7 (by decide), hsh 7]; rfl) h11 (hsh 11) rfl
  -- the counter word
  have g1 := fun j (h9' : j ≠ 9) (h7' : j ≠ 7) => c1.same j h9' h7'
  obtain ⟨τ2, s2, c2⟩ := cnt_spec cap n hc1 τ1 (by rw [(g1 8 (by decide) (by decide)).1, hbl 8 (by decide)])
    (by rw [(g1 8 (by decide) (by decide)).2, hsh 8]) (by rw [(g1 11 (by decide) (by decide)).1, h11])
    (by rw [(g1 11 (by decide) (by decide)).2, hsh 11]) (by rw [c1.val]; rfl)
  have g2 := only_of_cp c2
  -- the second coordinate
  obtain ⟨τ3, s3, e31, e39, eh39, e310, eh310, e312, eh312, v3, o3, cl3⟩ := pad_spec cap 1 (by decide)
    (by decide) (by decide) b2 (frameP lw) (frameP b1 ++ [false]) R (by rw [hl2]; exact hR) hc2 τ2
    (by rw [(g2 9 (by decide)).1, c1.st, h9, hw]) (by rw [(g2 9 (by decide)).2, c1.sh, hsh 9, Nat.zero_add])
    (by rw [(g2 1 (by decide)).1, (g1 1 (by decide) (by decide)).1, hbl 1 (by decide)])
    (by rw [(g2 1 (by decide)).2, (g1 1 (by decide) (by decide)).2, hsh 1])
    (by rw [(g2 10 (by decide)).1, (g1 10 (by decide) (by decide)).1, h10, hl2])
    (by rw [(g2 10 (by decide)).2, (g1 10 (by decide) (by decide)).2, hsh 10])
    (by rw [(g2 12 (by decide)).1, (g1 12 (by decide) (by decide)).1, h12])
    (by rw [(g2 12 (by decide)).2, (g1 12 (by decide) (by decide)).2, hsh 12])
    (by rw [c2.val, c1.val]; rfl)
  -- the first coordinate
  obtain ⟨τ4, s4, e40, e49, eh49, e410, eh410, e412, eh412, v4, o4, cl4⟩ := pad_spec cap 0 (by decide)
    (by decide) (by decide) b1 (frameP lw ++ frameP b2) [false] R (by rw [hl1]; exact hR) hc2 τ3
    (by rw [e39, (g2 9 (by decide)).1, c1.st, h9, hw]; simp only [List.append_assoc])
    (by rw [eh39, List.length_append, fpl, fpl, hl2])
    (by rw [(o3 0 (by decide) (by decide) (by decide) (by decide)).1, (g2 0 (by decide)).1,
      (g1 0 (by decide) (by decide)).1, hbl 0 (by decide)])
    (by rw [(o3 0 (by decide) (by decide) (by decide) (by decide)).2, (g2 0 (by decide)).2,
      (g1 0 (by decide) (by decide)).2, hsh 0])
    (by rw [e310, (g2 10 (by decide)).1, (g1 10 (by decide) (by decide)).1, h10, hl1]) eh310
    (by rw [e312, (g2 12 (by decide)).1, (g1 12 (by decide) (by decide)).1, h12]) eh312 v3
  rw [hl2] at s3
  rw [hl1] at s4
  -- the work tapes
  have k : ∀ j : Fin 14, j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 7 → j.val ≠ 8 → 13 < j.val ∨ j.val < 9 →
      τ4.st j = [] ∧ τ4.sh j = 0 := by
    intro j j0 j1 j7 j8 jr
    have j9 : j ≠ 9 := fun h => by subst h; simp at jr
    have j10 : j ≠ 10 := fun h => by subst h; simp at jr
    have j12 : j ≠ 12 := fun h => by subst h; simp at jr
    have a4 := o4 j (fun h => j0 (congrArg Fin.val h)) j9 j10 j12
    have a3 := o3 j (fun h => j1 (congrArg Fin.val h)) j9 j10 j12
    have a2 := g2 j (fun h => j8 (congrArg Fin.val h))
    have a1 := g1 j j9 (fun h => j7 (congrArg Fin.val h))
    have hj9 : j.val < 9 := by have := j.isLt; omega
    exact ⟨by rw [a4.1, a3.1, a2.1, a1.1, hbl j hj9], by rw [a4.2, a3.2, a2.2, a1.2, hsh j]⟩
  obtain ⟨τ5, s5, t2, t3, t4, t5, t6, o5, v5, cl5⟩ := tapes_spec cap R LW hc2 hc3 τ4
    (k 2 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (k 2 (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (k 3 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (k 3 (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (k 4 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (k 4 (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (k 5 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (k 5 (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (k 6 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (k 6 (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (by rw [e412, e312, (g2 12 (by decide)).1, (g1 12 (by decide) (by decide)).1, h12]) eh412
    (by rw [(o4 13 (by decide) (by decide) (by decide) (by decide)).1, (o3 13 (by decide) (by decide) (by decide)
      (by decide)).1, (g2 13 (by decide)).1, (g1 13 (by decide) (by decide)).1, h13])
    (by rw [(o4 13 (by decide) (by decide) (by decide) (by decide)).2, (o3 13 (by decide) (by decide) (by decide)
      (by decide)).2, (g2 13 (by decide)).2, (g1 13 (by decide) (by decide)).2, hsh 13]) v4
  have q := fun (j : Fin 14) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h5 : j ≠ 5) (h6 : j ≠ 6) => o5 j h2 h3 h4 h5 h6
  refine ⟨τ5, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5))), ?_, ?_, t2, t3, t4, t5, t6, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, v5, ?_⟩
  · rw [(q 0 (by decide) (by decide) (by decide) (by decide) (by decide)).1, e40]
  · rw [(q 1 (by decide) (by decide) (by decide) (by decide) (by decide)).1,
      (o4 1 (by decide) (by decide) (by decide) (by decide)).1, e31]
  · rw [(q 7 (by decide) (by decide) (by decide) (by decide) (by decide)).1,
      (o4 7 (by decide) (by decide) (by decide) (by decide)).1, (o3 7 (by decide) (by decide) (by decide)
      (by decide)).1, (g2 7 (by decide)).1, c1.out, hbl 7 (by decide), List.nil_append]
  · rw [(q 8 (by decide) (by decide) (by decide) (by decide) (by decide)).1,
      (o4 8 (by decide) (by decide) (by decide) (by decide)).1, (o3 8 (by decide) (by decide) (by decide)
      (by decide)).1, c2.out, (g1 8 (by decide) (by decide)).1, hbl 8 (by decide), List.nil_append]
  · rw [(q 9 (by decide) (by decide) (by decide) (by decide) (by decide)).1, e49, e39, (g2 9 (by decide)).1, c1.st, h9]
  · rw [(q 10 (by decide) (by decide) (by decide) (by decide) (by decide)).1, e410, e310, (g2 10 (by decide)).1,
      (g1 10 (by decide) (by decide)).1, h10]
  · rw [(q 11 (by decide) (by decide) (by decide) (by decide) (by decide)).1,
      (o4 11 (by decide) (by decide) (by decide) (by decide)).1, (o3 11 (by decide) (by decide) (by decide)
      (by decide)).1, (g2 11 (by decide)).1, (g1 11 (by decide) (by decide)).1, h11]
  · rw [(q 12 (by decide) (by decide) (by decide) (by decide) (by decide)).1, e412, e312, (g2 12 (by decide)).1,
      (g1 12 (by decide) (by decide)).1, h12]
  · rw [(q 13 (by decide) (by decide) (by decide) (by decide) (by decide)).1,
      (o4 13 (by decide) (by decide) (by decide) (by decide)).1, (o3 13 (by decide) (by decide) (by decide)
      (by decide)).1, (g2 13 (by decide)).1, (g1 13 (by decide) (by decide)).1, h13]
  · rw [cl5, cl4, cl3, c2.cell, c1.cell]; rfl

end NearCubicWires.WireExponent3_5.UnionMachine.WalkRun
