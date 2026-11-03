import Platform.RecLoopJ
import Platform.Hoare
import Platform.OutX
import Platform.CopyN

/-! # Register arithmetic and whole-stream copies

`addR A B T`: `B := B + A` (`A` kept, `T` scratch `0`), **`addR_spec`**. `mulR A A2 B C T`: `C := C + A·B`,
**`mulR_spec`**. `copyAll I Wk O …`: append every record of the record stream on `I` (any tail) to the output stream
`O`, **`copyAll_spec`**. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Platform
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-- `B := B + A`, `A` kept (`T` is `0` before and after). -/
def addR (A B T : Fin nr) : WMX ns nr :=
  .seq (.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup A B T)) (.wm (WM.move T A))

theorem addR_spec (cap : ℕ) {A B T : Fin nr} (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T) (σ : WState ns nr)
    (hT : σ.val T = 0) (hcap : σ.val B + σ.val A ≤ cap) :
    WXExec cap (addR A B T) σ (σ.setv B (σ.val B + σ.val A)) (18 * σ.val A + 3) := by
  have h1 := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup_spec (cap := cap) A B T hAB hAT hBT (σ.val A) σ rfl
    (by omega) (by omega) (by rw [hT]; omega)
  have h2 := wmove_spec (cap := cap) T A (Ne.symm hAT) (σ.val A)
    (((σ.setv A 0).setv B (σ.val B + σ.val A)).setv T (σ.val T + σ.val A)) (by simp [hT])
    (by simp [hT]; omega) (by simp [Function.update_apply, hAT, hAB, hT]; omega)
  refine (WXExec.seq (WXExec.wm h1) (WXExec.wm h2)).cast cap ?_ (by omega)
  apply WState.eq <;> try rfl
  funext r
  simp only [WState.setv_val, Function.update_apply]
  by_cases r1 : r = A
  · rw [r1]; simp [hAB, hAT, hT, Ne.symm hAT]
  · by_cases r2 : r = T
    · rw [r2]; simp [Ne.symm hAT, Ne.symm hBT, hT]
    · simp [r1, r2]

/-- `C := C + A·B` (`A2`, `T` scratch `0`; `A`, `B` kept). -/
def mulR (A A2 B C T : Fin nr) : WMX ns nr := repK A A2 (addR B C T)

theorem mulR_spec (cap : ℕ) {A A2 B C T : Fin nr} (hR : [A, A2, B, C, T].Nodup) (σ : WState ns nr)
    (hA2 : σ.val A2 = 0) (hT : σ.val T = 0) (hcap : σ.val C + σ.val A * σ.val B ≤ cap) (hcapA : 2 * σ.val A ≤ cap) :
    WXExec cap (mulR A A2 B C T) σ (σ.setv C (σ.val C + σ.val A * σ.val B))
      (σ.val A * (18 * σ.val B + 3 + 8) + 7 * σ.val A + 3) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hR
  have hst := Runs.repE (cap := cap) (K := A) (K2 := A2) (body := addR B C T) h1 (18 * σ.val B + 3) (σ.val A)
    (fun k => σ.setv C (σ.val C + k * σ.val B)) (by omega)
    (fun k => by simp [Function.update_apply, h3])
    (fun k => by simp [Function.update_apply, h6])
    (fun k hk v1 v2 => by
      have hh := addR_spec cap (A := B) (B := C) (T := T) h8 h9 h10
        (((σ.setv C (σ.val C + k * σ.val B)).setv A v1).setv A2 v2)
        (by simp [Function.update_apply, Ne.symm h10, Ne.symm h4, Ne.symm h7, hT])
        (by
          simp [Function.update_apply, Ne.symm h3, Ne.symm h6, h8, Ne.symm h2, Ne.symm h5]
          have : k * σ.val B + σ.val B ≤ σ.val A * σ.val B := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
          omega)
      have eb : (((σ.setv C (σ.val C + k * σ.val B)).setv A v1).setv A2 v2).val B = σ.val B := by
        simp [Function.update_apply, Ne.symm h2, Ne.symm h5, h8]
      rw [eb] at hh
      refine hh.cast cap ?_ le_rfl
      apply WState.eq <;> try rfl
      funext r
      simp only [WState.setv_val, Function.update_apply]
      by_cases r1 : r = C
      · rw [r1]; simp [Ne.symm h3, Ne.symm h6, h8]; ring
      · simp [r1])
    (by simp [Function.update_apply, h3]) (by simp [Function.update_apply, h6, hA2])
  have e0 : σ.setv C (σ.val C + 0 * σ.val B) = σ := by simp [BinW.setv_same]
  rw [e0] at hst
  exact hst

end NearCubicGates.Close.Platform

namespace NearCubicGates.Close.Platform
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StablePartition.Workspace (overlay)

end NearCubicGates.Close.Platform
