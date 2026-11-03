import CheckedPCPP.Harness
import CheckedPCPP.WMXReady
import Gadget.CheckedNodes
import Gadget.ThreeQuery
import Mathlib.Computability.TuringMachine.Computable
import Platform.Hoare
import Platform.RegArith
import Proof.CaseAnalysis.CaseTwoRequestInput
import Proof.Foundations.OrdinaryMachine
import Proof.Foundations.SourceCore
import Proof.Wire_3_5.Primitive.Writers.WriteNat
import CheckedPCPP.NodeEmit

/-!
# H3a set-up (R3.h3as): the encoder as a word function, the bound `B`, the driver and log streams

`encCols_runs` (H3a) needs: the framed encoder `Enc` of J8 (the near-cubic-gates paper, "a polynomial-time computable linear
encoding") as an ordinary word function `wf` (from `P.encPoly` by the framed bridge,
`FramedSim.tm2Poly_ordinary`), a bound `B ≥ |frame (messageWord ⟨q, e_i⟩)| + budget + 1` and `B ≥ 2·L` (J8
`codeLength`), a driver stream `1^B` and a log stream `0^B`. Here: `encWord P` packages `wf` with its polynomial budget
`K·(q + 1)^e`; `bound P q = Cb·(q + 1)^eb` is such a `B` for every `q ≥ 2` (`bound_ok`); `powW` computes it in a
register from `q`; `fillW` writes `1^B` and `0^B` (`setupW_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.EncSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.Platform
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget

/-! ## The encoder as a word function with a polynomial budget -/

/-! ## The bound `B` -/

/-! ## Computing `B` in a register -/

variable {ns nr : ℕ} (cap : ℕ)

/-- `Y := Y·X` (`Z`, `A2`, `T` scratch, `0` before and after). -/
def mulStep (X Y Z A2 T : Fin nr) : WMX ns nr :=
  .seq (mulR Y A2 X Z T) (.seq (.wm (WM.clear Y)) (.wm (WM.move Z Y)))

theorem mulStep_spec {X Y Z A2 T : Fin nr} (hR : [Y, A2, X, Z, T].Nodup) (σ : WState ns nr)
    (hZ : σ.val Z = 0) (hA2 : σ.val A2 = 0) (hT : σ.val T = 0) (hcap : σ.val Y * σ.val X + σ.val Y ≤ cap)
    (hcapY : 2 * σ.val Y ≤ cap) :
    WXExec cap (mulStep X Y Z A2 T) σ (σ.setv Y (σ.val Y * σ.val X))
      (σ.val Y * (18 * σ.val X + 3 + 8) + 7 * σ.val Y + 3 + 1 + (3 * σ.val Y + 1) + 1 + (7 * (σ.val Y * σ.val X) + 1)) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR'
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hR'
  have e1 := mulR_spec cap (A := Y) (A2 := A2) (B := X) (C := Z) (T := T) hR σ hA2 hT (by rw [hZ]; nlinarith)
    (by omega)
  rw [hZ, Nat.zero_add] at e1
  have hYZ : (σ.setv Z (σ.val Y * σ.val X)).val Y = σ.val Y := by
    simp only [WState.setv_val]; exact Function.update_of_ne h3 _ _
  have e2 := wclear_spec (cap := cap) Y (σ.val Y) (σ.setv Z (σ.val Y * σ.val X)) hYZ (by rw [hYZ]; omega)
  have e3 := wmove_spec (cap := cap) Z Y (Ne.symm h3) (σ.val Y * σ.val X)
    ((σ.setv Z (σ.val Y * σ.val X)).setv Y 0) (by simp [Function.update_of_ne (Ne.symm h3)])
    (by simp [Function.update_of_ne (Ne.symm h3)]; nlinarith) (by simp [Function.update_of_ne (Ne.symm h3)]; nlinarith)
  refine (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.wm e3))).cast cap ?_ (by omega)
  apply WState.eq <;> try rfl
  funext r
  simp only [WState.setv_val, Function.update_apply]
  split_ifs <;> simp_all

/-- `Y := Y·X^k`. -/
def powW (X Y Z A2 T : Fin nr) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | k + 1 => .seq (mulStep X Y Z A2 T) (powW X Y Z A2 T k)

/-- A crude cost bound of `powW` when every intermediate value is at most `W`. -/
def powCost (W k : ℕ) : ℕ := k * (40 * W * W + 40 * W + 20)

theorem powW_spec {X Y Z A2 T : Fin nr} (hR : [Y, A2, X, Z, T].Nodup) (W : ℕ) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val Z = 0 → σ.val A2 = 0 → σ.val T = 0 →
      σ.val Y * σ.val X ^ k ≤ W → 1 ≤ σ.val X → 2 * W + W * W ≤ cap →
      WXExec cap (powW X Y Z A2 T k) σ (σ.setv Y (σ.val Y * σ.val X ^ k)) (powCost W k)
  | 0, σ, _, _, _, _, _, _ => by
    simp only [powW, pow_zero, Nat.mul_one, wsetv_same, powCost, Nat.zero_mul]
    exact WXExec.skip cap σ
  | k + 1, σ, hZ, hA2, hT, hW, hX, hcap => by
    have hR' := hR
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
      and_true] at hR'
    obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hR'
    have hpk : 1 ≤ σ.val X ^ k := Nat.one_le_pow _ _ hX
    have hYX : σ.val Y * σ.val X ≤ W := by
      calc σ.val Y * σ.val X ≤ σ.val Y * σ.val X * σ.val X ^ k := Nat.le_mul_of_pos_right _ hpk
        _ = σ.val Y * σ.val X ^ (k + 1) := by ring
        _ ≤ W := hW
    have hY : σ.val Y ≤ W := le_trans (Nat.le_mul_of_pos_right _ hX) hYX
    have hXW : σ.val X ≤ W ∨ σ.val Y = 0 := by
      rcases Nat.eq_zero_or_pos (σ.val Y) with h | h
      · exact Or.inr h
      · exact Or.inl (le_trans (Nat.le_mul_of_pos_left _ h) hYX)
    have e1 := mulStep_spec cap hR σ hZ hA2 hT (by nlinarith) (by nlinarith)
    have ih := powW_spec hR W k (σ.setv Y (σ.val Y * σ.val X))
      (by simp [Function.update_of_ne (Ne.symm h3), hZ]) (by simp [Function.update_of_ne (Ne.symm h1), hA2])
      (by simp [Function.update_of_ne (Ne.symm h4), hT])
      (by
        simp only [WState.setv_val, Function.update_self, Function.update_of_ne (Ne.symm h2)]
        calc σ.val Y * σ.val X * σ.val X ^ k = σ.val Y * σ.val X ^ (k + 1) := by ring
            _ ≤ W := hW)
      (by simp only [WState.setv_val, Function.update_of_ne (Ne.symm h2)]; exact hX) hcap
    refine (WXExec.seq e1 ih).cast cap ?_ ?_
    · rw [wsetv_setv]
      simp only [WState.setv_val, Function.update_self, Function.update_of_ne (Ne.symm h2)]
      ring_nf
    · unfold powCost
      rcases hXW with hXW | hY0
      · have : σ.val Y * (18 * σ.val X + 3 + 8) ≤ 18 * W * W + 11 * W := by nlinarith
        nlinarith
      · rw [hY0]; simp; nlinarith

end NearCubicGates.Close.CheckedPCPP.EncSetup
