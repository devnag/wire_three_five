import Setup.Words
import Recovery.HTParts3
import CheckedPCPP.EmitNat
import CheckedPCPP.NodeEmit
import Platform.BinW

/-!
# W3c, phase A: the length guard and the witness prefix (c2)

From the cold start (`frame x` on `X`, `frame bits` on `BW`):
* `phA0`: `N := |x|` into `rN` (`BinW.width`, `frame x` read as the width-`N` number `value x`), the guard flag
  `[N0 ≤ N]` into `gF` (`leW`);
* `phA1` (on the guard): `K := ⌊N/16⌋` (four halvings), the first `K` witness bits raw onto `WT`
  (`Codec.unframeW_spec`, the near-cubic-gates paper: the guess lies in the first `⌊N/16⌋` witness bits), both heads back at
  `0`, every scratch register `0` again (`phA1_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Recovery.HTParts (leW leW_exec)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-! ## The cold state -/

section Cold
variable (D : SetupData s P g) (xs bits : List Bool)

@[simp] theorem coldState_sh : (coldState D xs bits).sh = fun _ => 0 := rfl
@[simp] theorem coldState_val : (coldState D xs bits).val = fun _ => 0 := rfl
@[simp] theorem coldState_cell : (coldState D xs bits).cell = false := rfl

end Cold

/-! ## Halving a register -/

/-- `X := X / 2` (`H`, `B` scratch at `0`). -/
def halfStep (X H B : Fin nrW) {ns : ℕ} : WMX ns nrW :=
  .seq (EmitNat.halve X H B) (.wm (.seq (WM.clear B) (WM.move H X)))

theorem halfStep_exec {ns cap : ℕ} {X H B : Fin nrW} (hXH : X ≠ H) (hXB : X ≠ B) (hHB : H ≠ B) (σ : WState ns nrW)
    (v : ℕ) (hv : σ.val X = v) (hH : σ.val H = 0) (hB : σ.val B = 0) (hc : 2 * v + 2 ≤ cap) :
    WXExec cap (halfStep X H B) σ (σ.setv X (v / 2)) (20 * v + 20) := by
  have e1 := EmitNat.halve_exec (cap := cap) X H B hXH hXB hHB v σ hv hB (by omega) (by omega) (by omega)
  set σ1 := ((σ.setv X 0).setv H (σ.val H + v / 2)).setv B (v % 2) with hσ1
  have e2 := WireExponent3_5.FinalPass.Tm.wclear_spec (cap := cap) B (v % 2) σ1 (by simp [hσ1])
    (by simp [hσ1]; omega)
  set σ2 := σ1.setv B 0 with hσ2
  have hX2 : σ2.val X = 0 := by simp [hσ2, hσ1, Function.update_apply, hXH, hXB]
  have hH2 : σ2.val H = v / 2 := by simp [hσ2, hσ1, Function.update_apply, hHB, hH]
  have e3 := WireExponent3_5.FinalPass.Tm.wmove_spec (cap := cap) H X (Ne.symm hXH) (v / 2) σ2 hH2 (by omega)
    (by omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.wm (WExec.seq e2 e3))) ?_ ?_
  · apply WState.eq <;> try rfl
    funext r
    simp only [hσ2, hσ1, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · have : v % 2 ≤ 1 := by omega
    have : v / 2 ≤ v := Nat.div_le_self _ _
    omega

/-- `X := X / 16`. -/
def div16 (X H B : Fin nrW) {ns : ℕ} : WMX ns nrW :=
  .seq (halfStep X H B) (.seq (halfStep X H B) (.seq (halfStep X H B) (halfStep X H B)))

theorem div16_exec {ns cap : ℕ} {X H B : Fin nrW} (hXH : X ≠ H) (hXB : X ≠ B) (hHB : H ≠ B) (σ : WState ns nrW)
    (v : ℕ) (hv : σ.val X = v) (hH : σ.val H = 0) (hB : σ.val B = 0) (hc : 2 * v + 2 ≤ cap) :
    WXExec cap (div16 X H B) σ (σ.setv X (v / 16)) (100 * v + 100) := by
  have hHv : ∀ (τ : WState ns nrW) (y : ℕ), (τ.setv X y).val H = τ.val H := fun τ y => by
    simp [Function.update_of_ne (Ne.symm hXH)]
  have hBv : ∀ (τ : WState ns nrW) (y : ℕ), (τ.setv X y).val B = τ.val B := fun τ y => by
    simp [Function.update_of_ne (Ne.symm hXB)]
  have e1 := halfStep_exec (cap := cap) hXH hXB hHB σ v hv hH hB hc
  have e2 := halfStep_exec (cap := cap) hXH hXB hHB (σ.setv X (v / 2)) (v / 2) (by simp) (by rw [hHv]; exact hH)
    (by rw [hBv]; exact hB) (by omega)
  have e3 := halfStep_exec (cap := cap) hXH hXB hHB ((σ.setv X (v / 2)).setv X (v / 2 / 2)) (v / 2 / 2) (by simp)
    (by rw [hHv, hHv]; exact hH) (by rw [hBv, hBv]; exact hB) (by omega)
  have e4 := halfStep_exec (cap := cap) hXH hXB hHB (((σ.setv X (v / 2)).setv X (v / 2 / 2)).setv X (v / 2 / 2 / 2))
    (v / 2 / 2 / 2) (by simp) (by rw [hHv, hHv, hHv]; exact hH) (by rw [hBv, hBv, hBv]; exact hB) (by omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))) ?_ ?_
  · simp only [LitDecode.setv_setv]
    congr 1
    omega
  · omega

/-! ## Registers of phase A -/

abbrev gN0 : Fin nrW := 49
abbrev gU : Fin nrW := 50
abbrev gK : Fin nrW := 51
abbrev gT : Fin nrW := 52
abbrev gF : Fin nrW := 53
abbrev kQ : Fin nrW := 54
abbrev dS : Fin nrW := 55
abbrev hH : Fin nrW := 56
abbrev hBr : Fin nrW := 57
abbrev oW : Fin nrW := 58
abbrev bR : Fin nrW := 59
abbrev tW : Fin nrW := 48

/-! ## Phase A, specs -/

end

end NearCubicGates.Close.Setup
