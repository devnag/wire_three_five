import Proof.Wire_3_5.FinalPass.WordLib

/-! # C6 front, U5: a register program leaves the registers it never names alone

For C5's register language (`WM`, `WExec`): **`WExec.frame_reg`**: if a program never names register `r`, a run of
it from `σ` to `τ` is also a run from `σ` with `r := x` to `τ` with `r := x`, at the same cost. The table writer uses
it to carry its loop counters through the loop bodies. Paper quantity: none (machine bookkeeping for P3:3685-3691). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTWFrame
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ} (cap : ℕ)

/-- Whether a program names register `r`. -/
def usesR (r : Fin nr) : WM ns nr → Bool
  | .skip => false
  | .inc r' => decide (r' = r)
  | .dec r' => decide (r' = r)
  | .fwd _ => false
  | .bwd _ => false
  | .wr _ _ => false
  | .setc _ => false
  | .seq P Q => usesR r P || usesR r Q
  | .ifr r' P Q => decide (r' = r) || usesR r P || usesR r Q
  | .ifs _ P Q => usesR r P || usesR r Q
  | .whr r' P => decide (r' = r) || usesR r P
  | .whs _ P => usesR r P

theorem setv_comm (σ : WState ns nr) (r r' : Fin nr) (h : r' ≠ r) (x y : ℕ) :
    (σ.setv r x).setv r' y = (σ.setv r' y).setv r x :=
  WState.eq rfl rfl (by simp only [WState.setv_val]; exact (Function.update_comm h y x σ.val).symm) rfl

theorem setv_seth (σ : WState ns nr) (r : Fin nr) (i : Fin (ns + 1)) (x y : ℕ) :
    (σ.setv r x).seth i y = (σ.seth i y).setv r x := rfl

theorem setv_sets (σ : WState ns nr) (r : Fin nr) (i : Fin (ns + 1)) (x : ℕ) (l : List Bool) :
    (σ.setv r x).sets i l = (σ.sets i l).setv r x := rfl

theorem setv_setc (σ : WState ns nr) (r : Fin nr) (x : ℕ) (c : Bool) :
    (σ.setv r x).setc c = (σ.setc c).setv r x := rfl

/-- **Framing a register**: a program that never names `r` runs the same with any value in `r`. -/
theorem WExec.frame_reg {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) (r : Fin nr)
    (hP : usesR r P = false) (x : ℕ) : WExec cap P (σ.setv r x) (τ.setv r x) n := by
  induction h with
  | skip σ => exact WExec.skip _
  | inc r' σ hc =>
    have hr : r' ≠ r := by simpa [usesR] using hP
    have e : ((σ.setv r' (σ.val r' + 1)).setv r x) = ((σ.setv r x).setv r' ((σ.setv r x).val r' + 1)) := by
      rw [wsetv_val_ne _ _ hr, setv_comm σ r r' hr]
    rw [e]
    exact WExec.inc r' _ (by rw [wsetv_val_ne _ _ hr]; exact hc)
  | dec r' σ hc =>
    have hr : r' ≠ r := by simpa [usesR] using hP
    have e : ((σ.setv r' (σ.val r' - 1)).setv r x) = ((σ.setv r x).setv r' ((σ.setv r x).val r' - 1)) := by
      rw [wsetv_val_ne _ _ hr, setv_comm σ r r' hr]
    rw [e]
    exact WExec.dec r' _ (by rw [wsetv_val_ne _ _ hr]; exact hc)
  | fwd i σ =>
    rw [← setv_seth]; exact WExec.fwd i _
  | bwd i σ =>
    rw [← setv_seth]; exact WExec.bwd i _
  | wr i b σ =>
    rw [← setv_sets]; exact WExec.wr i b _
  | setc v σ =>
    rw [← setv_setc]; exact WExec.setc v _
  | seq h1 h2 ih1 ih2 =>
    simp only [usesR, Bool.or_eq_false_iff] at hP
    exact WExec.seq (ih1 hP.1) (ih2 hP.2)
  | ifrT hv h1 ih =>
    simp only [usesR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hP
    exact WExec.ifrT (by rw [wsetv_val_ne _ _ hP.1.1]; exact hv) (ih hP.1.2)
  | ifrF hv h1 ih =>
    simp only [usesR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hP
    exact WExec.ifrF (by rw [wsetv_val_ne _ _ hP.1.1]; exact hv) (ih hP.2)
  | ifsT hv h1 ih =>
    simp only [usesR, Bool.or_eq_false_iff] at hP
    exact WExec.ifsT (by rw [wsbit_setv]; exact hv) (ih hP.1)
  | ifsF hv h1 ih =>
    simp only [usesR, Bool.or_eq_false_iff] at hP
    exact WExec.ifsF (by rw [wsbit_setv]; exact hv) (ih hP.2)
  | whrF hv =>
    simp only [usesR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hP
    exact WExec.whrF (by rw [wsetv_val_ne _ _ hP.1]; exact hv)
  | whrT hv h1 h2 ih1 ih2 =>
    have hP' := hP
    simp only [usesR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hP'
    exact WExec.whrT (by rw [wsetv_val_ne _ _ hP'.1]; exact hv) (ih1 hP'.2) (ih2 hP)
  | whsF hv =>
    exact WExec.whsF (by rw [wsbit_setv]; exact hv)
  | whsT hv h1 h2 ih1 ih2 =>
    have hP' := hP
    simp only [usesR] at hP'
    exact WExec.whsT (by rw [wsbit_setv]; exact hv) (ih1 hP') (ih2 hP)
  | mono h1 hle ih => exact WExec.mono (ih hP) hle

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTWFrame
