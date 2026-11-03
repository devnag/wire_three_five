import Codec.FieldInt

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Positions and repeated reads -/

/-- `i` steps of a position map. -/
def iter (nxt : ℕ → ℕ) : ℕ → ℕ → ℕ
  | p, 0 => p
  | p, i + 1 => iter nxt (nxt p) i

/-! ## Duplicating a register -/

/-- `C := C + Q` (`Q` kept, scratch `D = 0` before and after). -/
def dupR (Q C D : Fin nr) : WM ns nr := .seq (.whr Q (.seq (.dec Q) (.seq (.inc C) (.inc D)))) (WM.move D Q)

theorem dupLoop_spec (Q C D : Fin nr) (hQC : Q ≠ C) (hQD : Q ≠ D) (hCD : C ≠ D) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val Q = m → m ≤ cap → σ.val C + m ≤ cap → σ.val D + m ≤ cap →
      WExec cap (.whr Q (.seq (.dec Q) (.seq (.inc C) (.inc D)))) σ
        (((σ.setv Q 0).setv C (σ.val C + m)).setv D (σ.val D + m)) (11 * m + 1)
  | 0, σ, h0, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    apply WState.eq <;> try rfl
    funext r; simp only [WState.setv_val, Function.update_apply]
    split_ifs with h1 h2 h3 <;> subst_vars <;> simp [h0]
  | m + 1, σ, hm, hc, hC, hD => by
    have e1 := WExec.dec (cap := cap) Q σ (by omega)
    set σ1 := σ.setv Q (σ.val Q - 1) with hσ1
    have e2 := WExec.inc (cap := cap) C σ1 (by simp [hσ1, Function.update_of_ne (Ne.symm hQC)]; omega)
    set σ2 := σ1.setv C (σ1.val C + 1) with hσ2
    have e3 := WExec.inc (cap := cap) D σ2 (by
      simp [hσ2, hσ1, Function.update_apply, Ne.symm hQD, Ne.symm hCD]; omega)
    set σ3 := σ2.setv D (σ2.val D + 1) with hσ3
    have hrest := dupLoop_spec Q C D hQC hQD hCD m σ3
      (by simp [hσ3, hσ2, hσ1, Function.update_apply, hQC, hQD]; omega) (by omega)
      (by simp [hσ3, hσ2, hσ1, Function.update_apply, hCD, Ne.symm hQC]; omega)
      (by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm hQD, Ne.symm hCD]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) hrest) ?_ (by omega)
    apply WState.eq <;> try rfl
    funext r
    simp only [hσ3, hσ2, hσ1, WState.setv_val, Function.update_apply]
    by_cases hr : r = D
    · simp [hr, hQC, hQD, hCD, Ne.symm hQC, Ne.symm hQD, Ne.symm hCD]; omega
    by_cases hr' : r = C
    · simp [hr, hr', hQC, hQD, hCD, Ne.symm hQC, Ne.symm hQD, Ne.symm hCD]; omega
    by_cases hr'' : r = Q
    · simp [hr, hr', hr'', hQC, hQD, hCD, Ne.symm hQC, Ne.symm hQD, Ne.symm hCD]
    · simp [hr, hr', hr'']

theorem dupR_spec (Q C D : Fin nr) (hQC : Q ≠ C) (hQD : Q ≠ D) (hCD : C ≠ D) (σ : WState ns nr)
    (hD : σ.val D = 0) (hc : σ.val Q + σ.val C ≤ cap) :
    WExec cap (dupR Q C D) σ (σ.setv C (σ.val C + σ.val Q)) (18 * σ.val Q + 3) := by
  set m := σ.val Q with hm
  have e1 := dupLoop_spec cap Q C D hQC hQD hCD m σ rfl (by omega) (by omega) (by omega)
  set σ1 := ((σ.setv Q 0).setv C (σ.val C + m)).setv D (σ.val D + m) with hσ1
  have e2 := wmove_spec cap D Q (Ne.symm hQD) m σ1 (by simp [hσ1, hD])
    (by simp [hσ1]; omega) (by simp [hσ1, Function.update_apply, hQC, hQD]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq <;> try rfl
  funext r
  simp only [hσ1, WState.setv_val, Function.update_apply]
  by_cases hr : r = Q
  · subst hr; simp [hQD, hQC, hD]; omega
  by_cases hr' : r = D
  · subst hr'; simp [hr, Ne.symm hCD, Ne.symm hQD, hD]
  by_cases hr'' : r = C
  · subst hr''; simp [hr, hr', Ne.symm hQC]
  · simp [hr, hr', hr'']

/-! ## The gate transcoder -/

def gateEnd (w : List Bool) (p q : ℕ) : ℕ := intEnd w (iter (intEnd w) p q)

end NearCubicGates.Close.Codec
