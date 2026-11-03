import Proof.Wire_3_5.Primitive.Writers.ThrFin1
import Proof.Wire_3_5.FinalPass.SampleRef

/-! # c4 THR block, the THR finisher's append, run

`faP` from `O = sampleWord kh S`, the count `1^{|S|}` and `marks hbF`: `O = sampleWord kh S ++ hbF`; under the masked
reset (`faM`) with every head back at `0` (**`fa_step`**).

Paper quantity of the main type: the THR seed word `sampleWord kh S ++ frame hb` (P3:2932-2937, 2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrFin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- **One frame skipped** (the marks, then the terminator). -/
theorem skipFrame_exec (x : List Bool) (b : Bank 3) (pre post : List Bool) (hA : b.A 0 = pre ++ frame x ++ post)
    (hH : b.H 0 = pre.length) :
    Exec skipFrameP b ⟨Function.update b.H 0 (pre.length + (frame x).length), b.A⟩ (5 * x.length + 3) := by
  have hA' : b.A 0 = pre ++ marks x ++ (false :: post) := by rw [hA, frame_eq]; simp
  have e1 := frame_exec x 0 b pre post hA' (by rw [hH]; simp) (Nat.zero_le _)
  set b1 : Bank 3 := ⟨Function.update b.H 0 (pre.length + 2 * x.length), b.A⟩ with hb1
  have e2 := Exec.act b1 (fun _ => none) (mv 0)
  have heq : b1.act (fun _ => none) (mv 0) = ⟨Function.update b.H 0 (pre.length + (frame x).length), b.A⟩ := by
    simp only [Bank.act, hb1, Bank.mk.injEq]
    constructor
    · funext j; by_cases hj : j = 0
      · subst hj; simp [mv, HeadMove.apply, frame_eq, marks]; omega
      · simp [mv, hj, HeadMove.apply]
    · trivial
  rw [heq] at e2
  exact Exec.mono (Exec.seq e1 e2) (by omega)

/-- **Every frame skipped**: frames of `kh ≥ 1` bits start with a marker; the end of the tape reads `0`. -/
theorem frames_exec (kh : ℕ) (hkh : 1 ≤ kh) : ∀ (E : List (List Bool)) (b : Bank 3) (pre : List Bool),
    (∀ x ∈ E, x.length = kh) → b.A 0 = pre ++ E.flatMap frame → b.H 0 = pre.length →
    Exec skipAllP b ⟨Function.update b.H 0 (pre.length + (E.flatMap frame).length), b.A⟩ (E.length * (5 * kh + 5) + 1)
  | [], b, pre, hE, hA, hH => by
    have hbit : b.bit 0 = false := by
      simp only [Bank.bit, hA, hH, List.flatMap_nil, List.append_nil, readTapeBit]
      rw [List.getD_eq_default _ _ (le_refl _)]
    have e : (⟨Function.update b.H 0 (pre.length + (([] : List (List Bool)).flatMap frame).length), b.A⟩ : Bank 3) = b := by
      cases b with
      | mk H A =>
        simp only [Bank.mk.injEq, and_true]
        funext j
        by_cases h0 : j = 0
        · subst h0; simp at hH ⊢; omega
        · simp [h0]
    rw [e]
    exact Exec.mono (Exec.loopF hbit) (by simp)
  | x :: E, b, pre, hE, hA, hH => by
    have hx : x.length = kh := hE x (List.mem_cons_self)
    have hbit : b.bit 0 = true := by
      obtain ⟨c, x', rfl⟩ : ∃ c x', x = c :: x' := by
        cases x with
        | nil => simp at hx; omega
        | cons c x' => exact ⟨c, x', rfl⟩
      simp only [Bank.bit, hA, hH, List.flatMap_cons, readTapeBit]
      rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simp [frame_eq, marks]
    have e1 := skipFrame_exec x b pre (E.flatMap frame) (by rw [hA]; simp) hH
    set b1 : Bank 3 := ⟨Function.update b.H 0 (pre.length + (frame x).length), b.A⟩ with hb1
    have e2 := frames_exec kh hkh E b1 (pre ++ frame x) (fun y hy => hE y (List.mem_cons_of_mem _ hy))
      (by rw [hb1]; simp only; rw [hA]; simp) (by rw [hb1]; simp)
    have heq : (⟨Function.update b1.H 0 ((pre ++ frame x).length + (E.flatMap frame).length), b1.A⟩ : Bank 3) =
        ⟨Function.update b.H 0 (pre.length + ((x :: E).flatMap frame).length), b.A⟩ := by
      simp only [Bank.mk.injEq]
      constructor
      · funext j
        by_cases h0 : j = 0
        · subst h0; simp; omega
        · simp [h0, hb1]
      · rw [hb1]
    rw [heq] at e2
    refine Exec.mono (Exec.loopT hbit e1 e2) ?_
    rw [hx]; simp only [List.length_cons]; ring_nf; omega

/-- The sample word as its frames. -/
theorem sampleWord_frames (kh : ℕ) : ∀ S : List (ℕ × ℕ), FinalPass.Sample.sampleWord kh S =
    (S.flatMap fun p => [binary kh p.1, binary kh p.2]).flatMap frame
  | [] => rfl
  | p :: S => by
    rw [List.flatMap_cons, List.flatMap_append, ← sampleWord_frames kh S]
    simp [FinalPass.Sample.sampleWord]

theorem sampleFrames_length (kh : ℕ) : ∀ S : List (ℕ × ℕ),
    (S.flatMap fun p => [binary kh p.1, binary kh p.2]).length = 2 * S.length
  | [] => rfl
  | p :: S => by
    rw [List.flatMap_cons, List.length_append, sampleFrames_length kh S]
    simp; ring

theorem sampleFrames_width (kh : ℕ) (S : List (ℕ × ℕ)) :
    ∀ x ∈ S.flatMap (fun p => [binary kh p.1, binary kh p.2]), x.length = kh := by
  intro x hx
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact FinalPass.Sample.binary_length'' kh p.1
  · exact FinalPass.Sample.binary_length'' kh p.2

end NearCubicWires.WireExponent3_5.PrimAsm.ThrFin
