import CheckedPCPP.LitDecode
import CheckedPCPP.WMXReady
import NearCubicGates.PublishedSources.PCPP
import Proof.MachineModel.FrameCopy
import Proof.MachineModel.FrameSkip

/-!
# R3.h9, the clause front end (shared by the hard table and the weak worker W3d)

imp:three-pcpp (the near-cubic-gates paper) outputs a list of three-literal clauses; the hard table (v2 lines
2428–2446) and the worker read clause `a mod 2^{rb}` of the repeated list. J8 writes the list as
`RawThreeQueryPCPP.word = frame proofBits.bits ++ frame randomBits.bits ++` three framed literal codes per clause
(`ClauseAccess.word_eq`). `frontW`, on the J8 word stream `J` (head `0`, contents only reading like the word) and
the clause index `a` in a register, reads `proofBits` and `randomBits` into registers (`LitDecode.binW`), computes
`2^{rb}` (`dblW`) and `c = a mod 2^{rb}` (`modW`), skips `c` clauses (`skipT`), decodes the three literals
(`LitDecode.litW`) and rewinds `J` (every head move is counted). **`front_exec`**: the end state is exactly
`frontState` (the eight output registers set, everything else as at the start).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CheckedPCPP.ClauseFront

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.Platform
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.SourceInterfaces NearCubicGates.PublishedSources.PCPP
open NearCubicGates.Close.CheckedPCPP.LitDecode

variable {ns nr : ℕ} {cap : ℕ}

/-! ## Doubling and remainders in registers -/

/-- `M := M · 2^K`, `K := 0` (`Q`, `T` scratch). -/
def dblW (M K Q T : Fin nr) : WMX ns nr := .whr K (.seq (WMX.dec K) (.seq (addR M Q T) (.wm (WM.move Q M))))

theorem dblW_exec {M K Q T : Fin nr} (hR : [M, K, Q, T].Nodup) (Mx : ℕ) (hMx : 2 * Mx ≤ cap) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val K = k → k ≤ cap → σ.val Q = 0 → σ.val T = 0 → σ.val M * 2 ^ k ≤ Mx →
      WXExec cap (dblW M K Q T) σ ((σ.setv K 0).setv M (σ.val M * 2 ^ k)) (k * (25 * Mx + 10) + 1)
  | 0, σ, hK, _, _, _, _ => by
    rw [show (σ.setv K 0).setv M (σ.val M * 2 ^ 0) = σ by
      rw [pow_zero, Nat.mul_one, ← hK, wsetv_same, wsetv_same]]
    exact WXExec.mono (WXExec.whrF hK) (by simp)
  | k + 1, σ, hK, hKc, hQ, hT, hM => by
    have hR' := hR
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true] at hR'
    obtain ⟨⟨mk, mq, mt⟩, ⟨kq, kt⟩, qt⟩ := hR'
    have km := Ne.symm mk; have qm := Ne.symm mq; have tm := Ne.symm mt
    have qk := Ne.symm kq; have tk := Ne.symm kt; have tq := Ne.symm qt
    have hp : σ.val M * 2 ^ k * 2 ≤ Mx := by rw [pow_succ] at hM; linarith
    have hMle : σ.val M ≤ σ.val M * 2 ^ k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
    have e1 := WXExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have e2 := addR_spec cap mq mt qt σ1 (by simp [hσ1, Function.update_apply, tk, hT])
      (by simp [hσ1, Function.update_apply, qk, mk, hQ]; omega)
    set σ2 := σ1.setv Q (σ1.val Q + σ1.val M) with hσ2
    have hM1 : σ1.val M = σ.val M := by simp [hσ1, Function.update_apply, mk]
    have hQ1 : σ1.val Q = 0 := by simp [hσ1, Function.update_apply, Ne.symm kq, hQ]
    have e3 := wmove_spec (cap := cap) Q M (Ne.symm mq) (σ.val M) σ2 (by simp [hσ2, hM1, hQ1])
      (by simp [hσ2, hM1, hQ1]; omega) (by simp [hσ2, hM1, hQ1, Function.update_apply, mq]; omega)
    set σ3 := (σ2.setv Q 0).setv M (σ2.val M + σ2.val Q) with hσ3
    have ih := dblW_exec hR Mx hMx k σ3 (by simp [hσ3, hσ2, hσ1, Function.update_apply, km, kq, hK])
      (by omega) (by simp [hσ3, Function.update_apply, qm]) (by simp [hσ3, hσ2, hσ1, Function.update_apply,
        tm, tq, tk, hT])
      (by simp [hσ3, hσ2, hσ1, Function.update_apply, mq, qm, mk, qk, hQ]; nlinarith)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq e1 (WXExec.seq e2 (WXExec.wm e3))) ih) ?_
      le_rfl) (by simp [hσ2, hM1, hQ1]; nlinarith)
    apply WState.eq <;> try rfl
    funext q
    simp only [hσ3, hσ2, hσ1, WState.setv_val, Function.update_apply]
    by_cases q1 : q = M
    · rw [q1]; simp [mq, mk, qm, qk, km, hQ, pow_succ]; ring
    · by_cases q2 : q = K
      · rw [q2]; simp [km]
      · by_cases q3 : q = Q
        · rw [q3]; simp [qm, qk, hQ]
        · simp [q1, q2, q3]

/-! ## Skipping framed fields (counted) -/

/-! ## The front end -/


theorem named {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n) :
    ∃ τ', τ' = τ ∧ WXExec cap P σ τ' n := ⟨τ, rfl, h⟩

end NearCubicGates.Close.CheckedPCPP.ClauseFront
