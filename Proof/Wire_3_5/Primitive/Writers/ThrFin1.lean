import Proof.Wire_3_5.Primitive.Writers.C3WAppend

/-! # c4 THR block, the THR finisher's append: the framed hash bits after the samples

The THR stage's output is `sampleWord kh S ++ frame hb` (`Plan.seedWord` at a THR call). C6's sample expansion writes
`sampleWord kh S`, which is `2|S|` frames of `kh ≥ 1` bits each. The program `faP` on three tapes (the output `O`, an
unused tape, the marked hash bits `marks hbF`) skips the frames of `O` while its scanned cell is a marker. Then it copies
the marked bits' payload to the end of `O`: `O = sampleWord kh S ++ hbF`. Under the masked reset (`faM`, every head back at `0`).

* `skipFrameP`, `skipAllP`, `copyP`, **`faP`**, `frame_exec`, `skipAll_exec`, `copy_exec`, **`fa_exec`**, `faM`,
  **`fa_step`**.

Paper quantity of the main type: the THR seed word `sampleWord kh S ++ frame hb` (the greedy sample, then the hash
bits; P3:2932-2937, 2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrFin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- Move tape `i` right. -/
def mv (i : Fin 3) : Fin 3 → HeadMove := fun j => if j = i then .right else .stay

/-- One cell right on tape `i`. -/
def rt (i : Fin 3) : Prog 3 := .act (fun _ => none) (mv i)

/-- Skip one frame on `O`. -/
def skipFrameP : Prog 3 := .seq (.loop 0 (.seq (rt 0) (rt 0))) (rt 0)

/-- Skip every frame of `O` (each frame's payload is nonempty, so its first cell is a marker `1`). -/
def skipAllP : Prog 3 := .loop 0 skipFrameP

/-- Write `b` on `O` and move right. -/
def wrO (b : Bool) : Prog 3 := .act (fun j => if j = 0 then some b else none) (mv 0)

/-- Copy the marked bits' payload to `O`. -/
def copyP : Prog 3 := .loop 2 (.seq (rt 2) (.seq (.ite 2 (wrO true) (wrO false)) (rt 2)))

/-- **The append program.** -/
def faP : Prog 3 := .seq skipAllP copyP

theorem frame_eq (x : List Bool) : frame x = marks x ++ [false] := (RankBody.marks_frame x).symm

theorem rt_H (b : Bank 3) (i j : Fin 3) : (b.act (fun _ => none) (mv i)).H j = if j = i then b.H j + 1 else b.H j := by
  by_cases h : j = i <;> simp [Bank.act, mv, h, HeadMove.apply]

theorem rt_A (b : Bank 3) (i : Fin 3) : (b.act (fun _ => none) (mv i)).A = b.A := by
  funext j; simp [Bank.act]

theorem rd_marks (pre x post : List Bool) (k : ℕ) (hk : k < x.length) :
    readTapeBit (pre ++ marks x ++ post) (pre.length + 2 * k) = true ∧
      readTapeBit (pre ++ marks x ++ post) (pre.length + 2 * k + 1) = x.getD k false := by
  induction x generalizing pre k with
  | nil => simp at hk
  | cons a x ih =>
    cases k with
    | zero => simp [marks, readTapeBit, List.getD_append_right]
    | succ k =>
      have h := ih (pre ++ [true, a]) k (by simp at hk; omega)
      have e : pre ++ marks (a :: x) ++ post = pre ++ [true, a] ++ marks x ++ post := by simp [marks]
      rw [e]
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      constructor
      · rw [show pre.length + 2 * (k + 1) = pre.length + (1 + 1) + 2 * k by ring]; exact h.1
      · rw [show pre.length + 2 * (k + 1) + 1 = pre.length + (1 + 1) + 2 * k + 1 by ring, h.2]; simp

/-- **One frame skipped.** -/
theorem frame_exec (x : List Bool) : ∀ (k : ℕ) (b : Bank 3) (pre post : List Bool),
    b.A 0 = pre ++ marks x ++ (false :: post) → b.H 0 = pre.length + 2 * k → k ≤ x.length →
    Exec (.loop 0 (.seq (rt 0) (rt 0))) b ⟨Function.update b.H 0 (pre.length + 2 * x.length), b.A⟩
      (5 * (x.length - k) + 1) := by
  intro k
  induction h : x.length - k generalizing k with
  | zero =>
    intro b pre post hA hH hk
    have hkx : k = x.length := by omega
    have hbit : b.bit 0 = false := by
      simp only [Bank.bit, hA, hH, hkx]
      rw [show pre ++ marks x ++ false :: post = (pre ++ marks x) ++ false :: post by simp]
      rw [readTapeBit, List.getD_append_right _ _ _ _ (by simp [marks]; omega)]
      have e0 : pre.length + 2 * x.length - (pre ++ marks x).length = 0 := by simp [marks]; omega
      rw [e0]; rfl
    have e : (⟨Function.update b.H 0 (pre.length + 2 * x.length), b.A⟩ : Bank 3) = b := by
      cases b; simp only [Bank.mk.injEq, and_true]
      funext j; by_cases hj : j = 0
      · subst hj; simp at hH ⊢; omega
      · simp [hj]
    rw [e]; exact Exec.loopF hbit
  | succ r ih =>
    intro b pre post hA hH hk
    have hkx : k < x.length := by omega
    have hbit : b.bit 0 = true := by
      simp only [Bank.bit, hA, hH]
      rw [show pre ++ marks x ++ false :: post = pre ++ marks x ++ (false :: post) from rfl]
      exact (rd_marks pre x (false :: post) k hkx).1
    set b1 := b.act (fun _ => none) (mv 0) with hb1
    set b2 := b1.act (fun _ => none) (mv 0) with hb2
    have e1 := Exec.act b (fun _ => none) (mv 0)
    have e2 := Exec.act b1 (fun _ => none) (mv 0)
    have hA2 : b2.A 0 = pre ++ marks x ++ (false :: post) := by rw [hb2, rt_A, hb1, rt_A, hA]
    have hH2 : b2.H 0 = pre.length + 2 * (k + 1) := by rw [hb2, rt_H, hb1, rt_H]; simp; omega
    have e3 := ih (k + 1) (by omega) b2 pre post hA2 hH2 (by omega)
    have heq : (⟨Function.update b2.H 0 (pre.length + 2 * x.length), b2.A⟩ : Bank 3) =
        ⟨Function.update b.H 0 (pre.length + 2 * x.length), b.A⟩ := by
      simp only [Bank.mk.injEq]
      constructor
      · funext j; by_cases hj : j = 0
        · subst hj; simp
        · simp [hj, hb2, hb1, rt_H]
      · rw [hb2, rt_A, hb1, rt_A]
    rw [heq] at e3
    exact Exec.mono (Exec.loopT hbit (Exec.seq e1 e2) e3) (by omega)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrFin
