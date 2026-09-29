import Proof.Wire_3_5.UnionMachine.RegRatMul
import Proof.Wire_3_5.Primitive.SeedFix.TabConv

/-! # C1.2: reading words — a table's next word, and a framed `ratWord` as two binary words

* **`copyAtB A I F R`**: `A := v` for the width-`W` word `frame (binary W v)` at the head of `I`; the head of `I`
  then moves past it, so consecutive calls walk a table of words (FinalPass `mapPassAt` + a frame skip).
* **`ratReadW I O R c f`** (`TabConv`): from the framed `ratWord q` (`q ≥ 0`) at the head of `I`,
  append `frame (binary h q.num.toNat) ++ frame (binary h q.den)` to `O` along the ruler `false :: 1^h` on `R`; the
  input head moves past the word. **`skipRatW I c`**: skip a framed `ratWord`. Both are stated as the moves
  `PrimT.Mv`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5 (ratWord)

variable {ns nr : ℕ}

/-! ## A table's next word -/

/-- Skip one framed word: walk its markers two cells at a time, then step over its end. -/
def skipFrameB (I : Fin (ns + 1)) : WM ns nr := .seq (.whs I (.seq (.fwd I) (.fwd I))) (.fwd I)

theorem skipLoopB_spec (cap : ℕ) (I : Fin (ns + 1)) (pre rest : List Bool) :
    ∀ (ws : List Bool) (σ : WState ns nr), σ.st I = pre ++ (frameP ws ++ false :: rest) →
      ∀ (k : ℕ), σ.sh I = pre.length + 2 * k → ∀ (j : ℕ), j + k = ws.length →
      WExec cap (.whs I (.seq (.fwd I) (.fwd I))) σ (σ.seth I (pre.length + 2 * ws.length)) (5 * j + 1) := by
  intro ws σ hI k hk j
  induction j generalizing σ k with
  | zero =>
    intro hj
    have e : σ.seth I (pre.length + 2 * ws.length) = σ := by
      rw [show pre.length + 2 * ws.length = σ.sh I by omega]; exact wseth_same σ I
    rw [e]
    refine WExec.whsF ?_
    simp only [wbit, hI, hk, show k = ws.length by omega]
    rw [rd_shift]
    exact readTapeBit_frameP_end ws rest
  | succ j ih =>
    intro hj
    have h1 := WExec.fwd (cap := cap) I σ
    have h2 := WExec.fwd (cap := cap) I (σ.seth I (σ.sh I + 1))
    set τ := (σ.seth I (σ.sh I + 1)).seth I ((σ.seth I (σ.sh I + 1)).sh I + 1) with hτ
    have hτI : τ.st I = pre ++ (frameP ws ++ false :: rest) := by simp [hτ, hI]
    have hτh : τ.sh I = pre.length + 2 * (k + 1) := by simp [hτ, hk]; omega
    have h3 := ih τ hτI (k + 1) hτh (by omega)
    have hm : wbit σ I = true := by
      simp only [wbit, hI, hk]
      rw [← List.append_assoc, show pre.length + 2 * k = pre.length + 2 * k by rfl]
      have := rd_marker pre ws (false :: rest) k (by omega)
      simpa using this
    refine WExec.cast cap (WExec.whsT hm (WExec.seq h1 h2) h3) ?_ (by omega)
    simp [hτ, wseth_seth]

theorem skipFrameB_spec (cap : ℕ) (I : Fin (ns + 1)) (pre ws rest : List Bool) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (frameP ws ++ false :: rest)) (hh : σ.sh I = pre.length) :
    WExec cap (skipFrameB I) σ (σ.seth I (pre.length + 2 * ws.length + 1)) (5 * ws.length + 3) := by
  have h1 := skipLoopB_spec cap I pre rest ws σ hI 0 (by simp [hh]) ws.length (by omega)
  have h2 := WExec.fwd (cap := cap) I (σ.seth I (pre.length + 2 * ws.length))
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  simp [wseth_seth]

/-- **`A := v` from the word at `I`'s head; `I` moves past it.** -/
def copyAtB (A I : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := .seq (mapPass copyOut keepS A I F R) (skipFrameB I)

theorem copyAtB_spec (cap W : ℕ) {A I : Fin (ns + 1)} {F R : Fin nr} (hAI : A ≠ I) (hFR : F ≠ R)
    (σ : WState ns nr) (a v : ℕ) (pre rest : List Bool) (hA : NumOn σ A W a)
    (hI : σ.st I = pre ++ frame (binary W v) ++ rest) (hIh : σ.sh I = pre.length) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (copyAtB A I F R) σ ((σ.sets A (frame (binary W v))).seth I (pre.length + 2 * W + 1))
      (46 * W + 7) := by
  have h1 := mapPassAt_spec cap copyOut keepS A I F R hAI hFR (by omega) (binary W a) (binary W v) [] pre []
    (false :: rest) false σ (by simp) (by simp [hA.1, frame_eq_frameP]) (by simp [hA.2])
    (by rw [hI, frame_eq_frameP]; simp) hIh (by simp [hF]) hR (by simp; omega)
  rw [mapS_copy _ _ _ (by simp)] at h1
  set σ1 := (σ.sets A ([] ++ frameP (binary W v) ++ false :: [])).setv F false.toNat with hσ1
  have h2 := skipFrameB_spec cap I pre (binary W v) rest σ1 (by simp [hσ1, Ne.symm hAI, hI, frame_eq_frameP])
    (by simp [hσ1, hIh])
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp; omega)
  simp only [hσ1, binary_length]
  apply WState.eq
  · rfl
  · funext x; simp only [WState.seth_st, WState.setv_st, WState.sets_st, Function.update_apply, frame_eq_frameP]
    split_ifs <;> simp_all
  · funext x; simp only [WState.seth_val, WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all
  · rfl

/-! ## A framed `ratWord` -/

/-- Skip the sign cells, then convert the numerator and the denominator. -/
def ratReadW (I O R : Fin (ns + 1)) (c f : Fin nr) : WM ns nr :=
  .seq (.fwd I) (.seq (.fwd I) (.seq (convNatW I O R c f cpyOut cpyNxt) (convNatW I O R c f cpyOut cpyNxt)))

theorem frameP_ratWord (q : ℚ) : frameP (ratWord q) =
    true :: decide (q.num < 0) :: (frameP (natWord q.num.natAbs) ++ frameP (natWord q.den)) := by
  unfold ratWord frameP
  rw [List.flatMap_append]
  rfl

/-- The reader's cost. -/
def ratReadCost (kn kd h : ℕ) : ℕ := countCost kn + countCost kd + 2 * wordCost h + 7

section Read
variable (cap : ℕ) (I O R : Fin (ns + 1)) (c f : Fin nr)
  (hIO : I ≠ O) (hIR : I ≠ R) (hOR : O ≠ R) (hcf : c ≠ f)
include hIO hIR hOR hcf

/-- **`ratReadW`**: `frame (binary h q.num.toNat) ++ frame (binary h q.den)` appended to `O`. -/
theorem ratReadW_spec (hcap : 1 ≤ cap) (pre rest : List Bool) (q : ℚ) (hq : 0 ≤ q) (h : ℕ) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (frameP (ratWord q) ++ rest)) (hIh : σ.sh I = pre.length) (hc : σ.val c = 0)
    (hf : σ.val f = 0) (hkn : natBitLength q.num.natAbs ≤ h) (hkd : natBitLength q.den ≤ h)
    (hcn : natBitLength q.num.natAbs ≤ cap) (hcd : natBitLength q.den ≤ cap)
    (hO : σ.sh O = (σ.st O).length) (hR : σ.st R = false :: List.replicate h true) (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (ratReadW I O R c f) σ τ (ratReadCost (natBitLength q.num.natAbs) (natBitLength q.den) h) ∧
      Mv I O R c f σ τ (pre.length + 2 * (ratWord q).length) (frame (binary h q.num.toNat) ++ frame (binary h q.den))
        0 0 0 := by
  have hn : ¬ q.num < 0 := by have := Rat.num_nonneg.mpr hq; omega
  obtain ⟨s1, m1⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf σ hO
  set σ1 := σ.seth I (σ.sh I + 1) with hσ1
  obtain ⟨s2, m2⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf σ1 m1.hO
  set σ2 := σ1.seth I (σ1.sh I + 1) with hσ2
  have hI2 : σ2.st I = (pre ++ [true, decide (q.num < 0)]) ++
      (frameP (natWord q.num.natAbs) ++ (frameP (natWord q.den) ++ rest)) := by
    rw [m2.sI, m1.sI, hI, frameP_ratWord]; simp
  have hIh2 : σ2.sh I = (pre ++ [true, decide (q.num < 0)]).length := by rw [m2.hI, m1.hI, hIh]; simp
  obtain ⟨σ3, s3, m3⟩ := convNatW_spec cap I O R c f hIO hIR hOR hcf hcap cpyOut cpyNxt
    (pre ++ [true, decide (q.num < 0)]) (frameP (natWord q.den) ++ rest) q.num.natAbs h false σ2 hI2 hIh2
    (by rw [m2.vc, m1.vc, hc]) (by rw [m2.vf, m1.vf, hf]; rfl) hkn hcn m2.hO (by rw [m2.sR, m1.sR, hR])
    (by rw [m2.hR, m1.hR, hRh])
  obtain ⟨τ, s4, m4⟩ := convNatW_spec cap I O R c f hIO hIR hOR hcf hcap cpyOut cpyNxt
    ((pre ++ [true, decide (q.num < 0)]) ++ frameP (natWord q.num.natAbs)) rest q.den h false σ3
    (by rw [m3.sI, hI2]; simp) (by rw [m3.hI]; simp; omega) m3.vc (by rw [m3.vf]; rfl) hkd hcd m3.hO
    (by rw [m3.sR, m2.sR, m1.sR, hR]) m3.hR
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by unfold ratReadCost; omega), ?_⟩
  refine ((m1.trans m2).trans m3).trans_eq m4 ?_ ?_ rfl rfl rfl
  · simp [ratWord, intWord]; omega
  · rw [cmap_cpy, cmap_cpy]
    have e : q.num.toNat = q.num.natAbs := by omega
    rw [e]; simp

end Read

end NearCubicWires.WireExponent3_5.UnionMachine.RegRat
