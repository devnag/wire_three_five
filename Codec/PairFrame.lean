import Codec.Frame
import Codec.Field
import Platform.Hoare

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Platform

variable {ns nr : ℕ} (cap : ℕ)

theorem frame_eq_marks (l : List Bool) : RepairOrdinary.frame l = marks l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [RepairOrdinary.frame, marks, ih]

/-- Frame one raw witness field (`countWord k ++ bits`, the guess format) onto `dst`: read the count into `K`, copy
the `k` bits as marks, close with `false`, so `dst` gains `frame bits` (`k = |bits|`). -/
def fieldFrameW (W dst : Fin (ns + 1)) (OP K : Fin nr) : WM ns nr :=
  .seq (countW W K) (.seq (frameStream W dst OP K) (emitC dst OP false))

theorem fieldFrameW_spec (W dst : Fin (ns + 1)) (hWd : W ≠ dst) (OP K : Fin nr) (hKO : K ≠ OP)
    (pre bits rest : List Bool) (σ : WState ns nr) (hst : σ.st W = pre ++ (Worker.Format.countWord bits.length ++ bits) ++ rest)
    (hsh : σ.sh W = pre.length) (hd : σ.sh dst = (σ.st dst).length) (hK : σ.val K = 0)
    (hc : σ.val OP + 2 * bits.length + 1 ≤ cap) (hb : bits.length ≤ cap) :
    WExec cap (fieldFrameW W dst OP K) σ
      ((appendO (σ.seth W (pre.length + bits.length + 1 + bits.length)) dst OP (RepairOrdinary.frame bits)))
      (7 * bits.length + 3 + 1 + (22 * bits.length + 1 + 1 + 7)) := by
  have hrc : Worker.Format.readCount ((σ.st W).drop (σ.sh W)) = (bits.length, bits ++ rest) := by
    rw [hst, hsh, List.append_assoc, List.drop_left, List.append_assoc]
    exact Worker.Format.readCount_word bits.length (bits ++ rest)
  have e1 := countW_spec cap W K σ (by rw [hrc, hK]; simp; exact hb)
  rw [hrc, hK, hsh] at e1
  simp only [Nat.zero_add] at e1
  set σ1 := (σ.seth W (pre.length + bits.length + 1)).setv K bits.length with hσ1
  have e2 := frameStream_spec cap W dst hWd OP K hKO bits (pre ++ Worker.Format.countWord bits.length) rest σ1
    (by simp [hσ1, hst, List.append_assoc])
    (by simp [hσ1, Worker.Format.countWord]; omega)
    (by simp [hσ1, Function.update_apply, hWd.symm, hd])
    (by simp [hσ1]) hb
    (by simp [hσ1, Function.update_of_ne hKO.symm]; omega)
  set σ2 := ((appendO σ1 dst OP (marks bits)).setv K 0).seth W ((pre ++ Worker.Format.countWord bits.length).length +
    bits.length) with hσ2
  have e3 := emitC_spec (cap := cap) dst OP false σ2
    (by simp [hσ2, hσ1, Function.update_apply, hWd.symm, hd, marks_length])
    (by simp [hσ2, hσ1, Function.update_of_ne hKO.symm, marks_length]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl
  apply WState.eq
  · funext y; by_cases hy : y = W
    · subst hy; simp [hσ2, hσ1, appendO, Function.update_apply, hWd, Worker.Format.countWord]; omega
    · by_cases hyd : y = dst
      · subst hyd; simp [hσ2, hσ1, appendO, Function.update_apply, hy, hd, marks_length, frame_eq_marks]; omega
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
  · funext y; by_cases hyd : y = dst
    · subst hyd; simp [hσ2, hσ1, appendO, Function.update_apply, hWd.symm, frame_eq_marks]
    · simp [hσ2, hσ1, appendO, Function.update_of_ne hyd]
  · funext r
    by_cases hr : r = OP
    · subst hr; simp [hσ2, hσ1, appendO, Function.update_apply, hKO.symm, frame_eq_marks, marks_length]; omega
    · by_cases hrK : r = K
      · subst hrK; simp [hσ2, hσ1, appendO, Function.update_apply, hr, hK]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hr, Function.update_of_ne hrK]
  · rfl

end NearCubicGates.Close.Codec
