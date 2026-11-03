import CheckedPCPP.WMXReady

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.Platform NearCubicWires.RepairRepresentation

namespace EmitNat

variable {ns nr : ℕ} {cap : ℕ}

/-- `X := 0`, `Y += X / 2`, `B := X % 2`. -/
def halve (X Y B : Fin nr) : WMX ns nr :=
  .whr X (.seq (WMX.dec X) (.ifr X (.seq (WMX.dec X) (WMX.inc Y)) (WMX.inc B)))

theorem halve_exec (X Y B : Fin nr) (hXY : X ≠ Y) (hXB : X ≠ B) (hYB : Y ≠ B) :
    ∀ v (σ : WState ns nr), σ.val X = v → σ.val B = 0 → σ.val Y + v ≤ cap → v ≤ cap → 1 ≤ cap →
      WXExec cap (halve X Y B) σ (((σ.setv X 0).setv Y (σ.val Y + v / 2)).setv B (v % 2)) (5 * v + 9)
  | 0, σ, hX, hB, _, _, _ => by
    have e : ((σ.setv X 0).setv Y (σ.val Y + 0 / 2)).setv B (0 % 2) = σ := by
      apply WState.eq <;> try rfl
      funext j; simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    rw [e]
    exact WXExec.mono (WXExec.whrF hX) (by omega)
  | 1, σ, hX, hB, hY, _, hc => by
    let σ1 := σ.setv X (σ.val X - 1)
    have h1 := WXExec.dec (cap := cap) X σ (by omega)
    have h2 := WXExec.inc (cap := cap) B σ1 (by simp [σ1, Function.update_apply, hXB.symm, hB]; omega)
    have hif := WXExec.ifrF (r := X) (P := .seq (WMX.dec X) (WMX.inc Y)) (by simp [σ1, hX]) h2
    let σ2 := σ1.setv B (σ1.val B + 1)
    have hend := WXExec.whrF (cap := cap) (r := X) (P := .seq (WMX.dec X) (.ifr X (.seq (WMX.dec X) (WMX.inc Y))
      (WMX.inc B))) (σ := σ2) (by simp [σ2, σ1, Function.update_apply, hXB, hX])
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq h1 hif) hend) ?_ le_rfl) (by omega)
    apply WState.eq <;> try rfl
    funext j; simp only [σ2, σ1, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  | k + 2, σ, hX, hB, hY, hv, hc => by
    let σ1 := σ.setv X (σ.val X - 1)
    have h1 := WXExec.dec (cap := cap) X σ (by omega)
    let σ2 := σ1.setv X (σ1.val X - 1)
    have h2 := WXExec.dec (cap := cap) X σ1 (by simp [σ1]; omega)
    have h3 := WXExec.inc (cap := cap) Y σ2 (by simp [σ2, σ1, Function.update_apply, hXY.symm]; omega)
    have hif := WXExec.ifrT (r := X) (Q := WMX.inc B) (by simp [σ1, hX]) (WXExec.seq h2 h3)
    let σ3 := σ2.setv Y (σ2.val Y + 1)
    have ih := halve_exec X Y B hXY hXB hYB k σ3 (by simp [σ3, σ2, σ1, Function.update_apply, hXY, hX])
      (by simp [σ3, σ2, σ1, Function.update_apply, hXB.symm, hYB.symm, hB])
      (by simp [σ3, σ2, σ1, Function.update_apply, hXY.symm]; omega) (by omega) hc
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq h1 hif) ih) ?_ le_rfl) (by omega)
    apply WState.eq <;> try rfl
    funext j; simp only [σ3, σ2, σ1, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega

section Output

end Output

end EmitNat

end NearCubicGates.Close.CheckedPCPP
