import Codec.Field

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

/-! ## The scan -/

/-! ## Rewind, subtract, emit, skip -/

/-- Append `marks (1^T)`, moving `T` into `U`. -/
def onesLoop (T U : Fin nr) (o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .whr T (.seq (.dec T) (.seq (.inc U) (emitPair o OP true)))

theorem onesLoop_spec (T U : Fin nr) (o : Fin (ns + 1)) (OP : Fin nr) (hTU : T ≠ U) (hTO : T ≠ OP) (hUO : U ≠ OP) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val T = m → σ.sh o = (σ.st o).length → m ≤ cap → σ.val U + m ≤ cap →
      σ.val OP + 2 * m ≤ cap →
      WExec cap (onesLoop T U o OP) σ (appendO ((σ.setv T 0).setv U (σ.val U + m)) o OP
        (marks (List.replicate m true))) (23 * m + 1)
  | 0, σ, h0, ho, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    rw [List.replicate_zero, show marks ([] : List Bool) = [] from rfl, WireExponent3_5.PrimAsm.WriteNat.appendO_nil]
    apply WState.eq
    · simp
    · simp
    · funext r
      by_cases hr : r = U
      · subst hr; simp
      by_cases hr' : r = T
      · subst hr'; simp [Function.update_of_ne hr, h0]
      · simp [Function.update_of_ne hr, Function.update_of_ne hr']
    · simp
  | m + 1, σ, hm, ho, hc, hU, hO => by
    have e1 := WExec.dec (cap := cap) T σ (by omega)
    set σ1 := σ.setv T (σ.val T - 1) with hσ1
    have e2 := WExec.inc (cap := cap) U σ1 (by simp [hσ1, Function.update_of_ne (Ne.symm hTU)]; omega)
    set σ2 := σ1.setv U (σ1.val U + 1) with hσ2
    have e3 := emitPair_spec cap o OP true σ2 (by simpa [hσ2, hσ1] using ho)
      (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hUO), Function.update_of_ne (Ne.symm hTO)]; omega)
    set σ3 := appendO σ2 o OP [true, true] with hσ3
    have hrest := onesLoop_spec T U o OP hTU hTO hUO m σ3
      (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hTO, Function.update_of_ne hTU]; omega)
      (by simp [hσ3, hσ2, hσ1, ho])
      (by omega)
      (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hUO, Function.update_of_ne (Ne.symm hTU)]; omega)
      (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hUO), Function.update_of_ne (Ne.symm hTO)]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) hrest) ?_ (by omega)
    have hmk : marks (List.replicate (m + 1) true) = [true, true] ++ marks (List.replicate m true) := by
      simp [List.replicate_succ, marks]
    apply WState.eq
    · funext j; by_cases hj : j = o
      · subst hj; simp [hσ3, hσ2, hσ1, appendO, hmk, marks_length]; omega
      · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj]
    · funext j; by_cases hj : j = o
      · subst hj; simp [hσ3, hσ2, hσ1, appendO, hmk]
      · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj]
    · funext r
      simp only [hσ3, hσ2, hσ1, appendO_val, WState.setv_val, Function.update_apply, hmk, List.length_append,
        marks_length, List.length_replicate, List.length_cons, List.length_nil]
      split_ifs <;> simp_all <;> omega
    · simp [hσ3, hσ2, hσ1]

/-! ## The number transcoder -/

/-- The field length at position `p`. -/
def fieldLen (w : List Bool) (p : ℕ) : ℕ := (readCount (w.drop p)).1

end NearCubicGates.Close.Codec
