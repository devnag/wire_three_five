import Platform.RecLoopJ

/-! # Writing records field by field into an output stream

A record whose word is the concatenation of several fixed-width numbers is written by appending each number's
marked bits (`fieldO`: the pairs of the framed word on `Src`, without its end marker) and then one `false`
(`emitO`). Both act on an output stream in `OutOn` form (written from its start over old contents). **`fieldO_spec`**,
**`emitO_spec`**; `outOn_after` packages the result. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Platform
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (copyPair emitB rst copyLoop_rst emitB_rst fwdA_rst rd_app0)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-- The state after the output stream `O` has been written up to `out` (head and counter at its end). -/
def outSt (σ : WState ns nr) (O : Fin (ns + 1)) (CO : Fin nr) (out L0 : List Bool) : WState ns nr :=
  ((σ.sets O (overlay out L0)).seth O out.length).setv CO out.length

theorem outOn_outSt (σ : WState ns nr) (O : Fin (ns + 1)) (CO : Fin nr) (out L0 : List Bool) :
    OutOn (outSt σ O CO out L0) O CO out L0 := ⟨by simp [outSt], by simp [outSt], by simp [outSt]⟩

theorem outSt_outSt (σ : WState ns nr) (O : Fin (ns + 1)) (CO : Fin nr) (out out' L0 L1 : List Bool) :
    outSt (outSt σ O CO out L0) O CO out' L1 = outSt σ O CO out' L1 := by
  apply WState.eq
  · funext i; by_cases hi : i = O
    · subst hi; simp [outSt]
    · simp [outSt, Function.update_of_ne hi]
  · funext i; by_cases hi : i = O
    · subst hi; simp [outSt]
    · simp [outSt, Function.update_of_ne hi]
  · funext r; by_cases hr : r = CO
    · subst hr; simp [outSt]
    · simp [outSt, Function.update_of_ne hr]
  · rfl

/-- A stream already in `OutOn` form is its own `outSt`. -/
theorem outSt_self (σ : WState ns nr) {O : Fin (ns + 1)} {CO : Fin nr} {out L0 : List Bool}
    (h : OutOn σ O CO out L0) : outSt σ O CO out L0 = σ := by
  apply WState.eq
  · funext i; by_cases hi : i = O
    · subst hi; simp [outSt, h.2.1]
    · simp [outSt, Function.update_of_ne hi]
  · funext i; by_cases hi : i = O
    · subst hi; simp [outSt, h.1]
    · simp [outSt, Function.update_of_ne hi]
  · funext r; by_cases hr : r = CO
    · subst hr; simp [outSt, h.2.2]
    · simp [outSt, Function.update_of_ne hr]
  · rfl

/-- Append one bit to an output stream. -/
def emitO (O : Fin (ns + 1)) (CO : Fin nr) (b : Bool) : WMX ns nr := .wm (emitB O CO b)

theorem emitO_spec (cap : ℕ) {O : Fin (ns + 1)} {CO : Fin nr} (σ : WState ns nr) (out L0 : List Bool) (b : Bool)
    (hO : OutOn σ O CO out L0) (hc : out.length < cap) :
    WXExec cap (emitO O CO b) σ (outSt σ O CO (out ++ [b]) L0) 7 := by
  have h1 := WExec.wr (cap := cap) O b σ
  rw [hO.1, hO.2.1, StablePartition.Workspace.overlay_write] at h1
  have h2 := wfwdC_spec cap O CO (σ.sets O (overlay (out ++ [b]) L0)) (by simp [hO.2.2]; exact hc)
  refine WXExec.wm (WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl)
  apply WState.eq
  · funext i; by_cases hi : i = O
    · subst hi; simp [outSt, hO.2.1]
    · simp [outSt, Function.update_of_ne hi]
  · rfl
  · funext r; by_cases hr : r = CO
    · subst hr; simp [outSt, hO.2.2]
    · simp [outSt, Function.update_of_ne hr]
  · rfl

end NearCubicGates.Close.Platform
