import Proof.Wire_3_5.Primitive.Writers.SBEmit
import Proof.Wire_3_5.Primitive.Writers.DataSetup
import Proof.Wire_3_5.Primitive.Writers.SparseNum

/-! # SB, part 15: the request's length `n` and mode bit, and the carrier counts

S4's small numbers start from the request's `n` and mode bit (`PrimRequest.word = natWord n ++ [mode] ++ …`,
`Data.reqW`) and the carrier counts (`1^c` streams of the carrier phase). On any word layout:

* `read_marks`, `read_marks_end`; `measureW`, **`measure_spec`** (`frame w`: head and `LEN` to `2|w|`);
* `parseW`, **`parse_spec`**: from `frame (reqW n mb codes cc tl)` (head `0`), `n` into `v`, the bit into `MB`, the head
  back at `0`, every scratch register back at `0`;
* `countW`, **`count_spec`**: `1^c` (head `0`) read into `R`, the head back at `0`.

Paper quantity of the main type: the request's `n` and class mode (P3:3068-3084, `PrimRequest.word`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBParse
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

theorem read_marks : ∀ (w t : List Bool) (k : ℕ), k < w.length →
    readTapeBit (Streaming.marks w ++ t) (2 * k) = true
  | [], _, k, hk => by simp at hk
  | b :: w, t, 0, _ => by simp [Streaming.marks, readTapeBit]
  | b :: w, t, k + 1, hk => by
    have ih := read_marks w t k (by simpa using hk)
    simp only [Streaming.marks, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    simp only [readTapeBit] at ih ⊢
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    simpa [List.getD] using ih

theorem read_marks_end : ∀ (w : List Bool), readTapeBit (Streaming.marks w ++ [false]) (2 * w.length) = false
  | [] => by simp [Streaming.marks, readTapeBit]
  | b :: w => by
    have ih := read_marks_end w
    simp only [Streaming.marks, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc,
      List.length_cons] at ih ⊢
    simp only [readTapeBit] at ih ⊢
    rw [show 2 * (w.length + 1) = 2 * w.length + 1 + 1 by ring]
    simpa [List.getD] using ih

variable {ns nr : ℕ} (cap : ℕ)

/-- Measure a framed word: two cells per bit. -/
def measureW (I : Fin (ns + 1)) (LEN : Fin nr) : WM ns nr :=
  .whs I (.seq (.fwd I) (.seq (.fwd I) (.seq (.inc LEN) (.inc LEN))))

theorem measure_spec (I : Fin (ns + 1)) (LEN : Fin nr) (w : List Bool) (σ : WState ns nr)
    (hst : σ.st I = frame w) (hsh : σ.sh I = 0) (hL : σ.val LEN = 0) (hc : 2 * w.length ≤ cap) :
    WExec cap (measureW I LEN) σ ((σ.seth I (2 * w.length)).setv LEN (2 * w.length)) (w.length * 13 + 1) := by
  set S : ℕ → WState ns nr := fun k => (σ.seth I (2 * k)).setv LEN (2 * k) with hS
  have hS0 : S 0 = σ := by
    apply WState.eq
    · funext j; by_cases hj : j = I
      · subst hj; simp [hS, hsh]
      · simp [hS, Function.update_of_ne hj]
    · rfl
    · funext j; by_cases hj : j = LEN
      · subst hj; simp [hS, hL]
      · simp [hS, Function.update_of_ne hj]
    · rfl
  have hfm : frame w = Streaming.marks w ++ [false] := by
    have h := Streaming.frame_append w []
    simpa [frame] using h
  have hT : ∀ k < w.length, wbit (S k) I = true := by
    intro k hk
    simp only [wbit, hS, WState.setv_st, WState.setv_sh, WState.seth_st, WState.seth_sh, Function.update_self, hst,
      hfm]
    exact read_marks w [false] k hk
  have hF : wbit (S w.length) I = false := by
    simp only [wbit, hS, WState.setv_st, WState.setv_sh, WState.seth_st, WState.seth_sh, Function.update_self, hst,
      hfm]
    exact read_marks_end w
  have hb : ∀ k < w.length, WExec cap (.seq (.fwd I) (.seq (.fwd I) (.seq (.inc LEN) (.inc LEN)))) (S k) (S (k + 1)) 11 := by
    intro k hk
    have e1 := WExec.fwd (cap := cap) I (S k)
    have e2 := WExec.fwd (cap := cap) I ((S k).seth I ((S k).sh I + 1))
    set T := ((S k).seth I ((S k).sh I + 1)).seth I (((S k).seth I ((S k).sh I + 1)).sh I + 1) with hT'
    have e3 := WExec.inc (cap := cap) LEN T (by simp [hT', hS]; omega)
    have e4 := WExec.inc (cap := cap) LEN (T.setv LEN (T.val LEN + 1)) (by simp [hT', hS]; omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl
    apply WState.eq
    · funext j; by_cases hj : j = I
      · subst hj; simp [hT', hS]; ring
      · simp [hT', hS, Function.update_of_ne hj]
    · rfl
    · funext j; by_cases hj : j = LEN
      · subst hj; simp [hT', hS]; ring
      · simp [hT', hS, Function.update_of_ne hj]
    · rfl
  have h := Data.whsLoop cap I _ 11 w.length S hT hF hb
  rw [hS0] at h
  exact WExec.mono h (by ring_nf; omega)

/-- Read `1^c` into `R` (position counter `C`), then rewind. -/
def countW (Sm : Fin (ns + 1)) (C R : Fin nr) : WM ns nr := .seq (WM.readU Sm C R) (WM.rewind Sm C)

theorem count_spec (Sm : Fin (ns + 1)) (C R : Fin nr) (hCR : C ≠ R) (c : ℕ) (σ : WState ns nr)
    (hst : σ.st Sm = List.replicate c true) (hsh : σ.sh Sm = 0) (hC : σ.val C = 0) (hR : σ.val R = 0)
    (hc : c + 1 ≤ cap) :
    WExec cap (countW Sm C R) σ (σ.setv R c) (11 * c + 7 + 1 + (5 * (c + 1) + 1)) := by
  have e1 := wreadU_spec cap Sm C R hCR c σ (fun k hk => by rw [hst, hsh, Data.rep_read]; simp; omega)
    (by rw [hst, hsh, Data.rep_read]; simp) (by omega) (by omega)
  set τ := ((σ.seth Sm (σ.sh Sm + c + 1)).setv C (σ.val C + c + 1)).setv R (σ.val R + c) with hτ
  have e2 := wrewind_spec cap Sm C (c + 1) τ (by simp [hτ, Function.update_of_ne hCR, hC] <;> omega)
    (by simp [hτ, Function.update_of_ne hCR, hC] <;> omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply WState.eq
  · funext j; by_cases hj : j = Sm
    · subst hj; simp [hτ, hsh]
    · simp [hτ, Function.update_of_ne hj]
  · rfl
  · funext j; by_cases hj : j = C
    · subst hj; simp [hτ, hCR, hC]
    · by_cases hj2 : j = R
      · subst hj2; simp [hτ, Function.update_of_ne hj, hR]
      · simp [hτ, Function.update_of_ne hj, Function.update_of_ne hj2]
  · rfl

end NearCubicWires.WireExponent3_5.PrimAsm.SBParse
