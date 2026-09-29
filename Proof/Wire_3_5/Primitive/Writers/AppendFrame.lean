import Proof.MachineModel.FrameCopy
import Proof.Wire_3_5.Primitive.Writers.Ruler

/-! # The two framing stages of PA.compose's glue (leaf-P kit)

* `copy_step`: base `FrameCopy` under base `Rewind` copies the framed request `frame w` to a fresh tape, all heads back
  at `0` (the first machine's entry tape; the request stays on tape `0` for the second machine).
* `append_step`: the append kernel reads `frame w`, the raw output `s` of the first machine and its unary length
  `replicate |s| true` (`PrimAsmRuler`), and writes `frame (w ++ s) = marks w ++ marks s ++ [false]`, the second
  machine's entry word; under base `Rewind`, all heads back at `0`. Kernel tapes: `0` frame w, `1` s, `2` ruler, `3` out.

Paper quantity of the main type: `frame (w ++ s)`, the final pass's input `req.word ++ seedWord` (`append_step`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.AppendFrame
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution

/-! ## The copy stage -/

/-- **The copy stage**: `frame w` on tape `0` is copied to tape `1`; all heads end at `0`. -/
theorem copy_step (w : List Bool) : ∃ tout : Fin (3 + 1) → List Bool,
    Step (Rewind.machine FrameCopy.machine) (8 * w.length + 10) (fun _ => 0)
      (Fin.addCases ![frame w, [], []] (fun _ => [])) (fun _ => 0) tout ∧
      tout 0 = frame w ∧ tout 1 = frame w := by
  obtain ⟨src, hsrc, hf, hs⟩ := FrameCopy.copy_run [] w []
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hsrc hf
  have hrun : run FrameCopy.machine (2 * (frame w).length + 2) ![frame w, [], []] = some src := by
    have he : FrameCopy.cfg 0 (frame w) 0 [] 0 [] 0 = initialConfiguration FrameCopy.machine ![frame w, [], []] := by
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    rw [he] at hsrc
    exact hsrc
  obtain ⟨r, hr, htapes, _, hheads, hsteps, _⟩ := Rewind.Workspace.reset_workspace FrameCopy.machine _ _ src hrun 0
  refine ⟨r.final.tapes, ⟨r, ?_, funext hheads, rfl, ?_⟩, ?_, ?_⟩
  · have e : 2 * src.steps + 2 = 8 * w.length + 10 := by rw [hs, frame_length]; ring
    rw [e] at hr
    exact hr
  · rw [hsteps, hs, frame_length]; omega
  · have h0 := htapes 0
    rw [hf] at h0
    exact h0
  · have h1 := htapes 1
    rw [hf] at h1
    exact h1

/-! ## The append kernel -/

def raw : Machine 4 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q bits =>
    if q.val = 0 then
      some (if bits 0 then ⟨1, ![none, none, none, some true], ![.right, .stay, .stay, .right]⟩
        else ⟨2, fun _ => none, fun _ => .stay⟩)
    else if q.val = 1 then some ⟨0, ![none, none, none, some (bits 0)], ![.right, .stay, .stay, .right]⟩
    else if q.val = 2 then
      some (if bits 2 then ⟨3, ![none, none, none, some true], ![.stay, .stay, .stay, .right]⟩
        else ⟨4, ![none, none, none, some false], ![.stay, .stay, .stay, .right]⟩)
    else if q.val = 3 then some ⟨2, ![none, none, none, some (bits 1)], ![.stay, .right, .right, .right]⟩
    else none

def acfg (q : Fin 5) (i y : ℕ) (IN S R Z : List Bool) : Configuration 4 5 := ⟨q, ![i, y, y, Z.length], ![IN, S, R, Z]⟩

theorem markA_step (i y : ℕ) (IN S R Z : List Bool) (h : readTapeBit IN i = true) :
    step raw (acfg 0 i y IN S R Z) = some (acfg 1 (i + 1) y IN S R (Z ++ [true])) := by
  simp [step, raw, acfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end]

theorem bitA_step (i y : ℕ) (IN S R Z : List Bool) :
    step raw (acfg 1 i y IN S R Z) = some (acfg 0 (i + 1) y IN S R (Z ++ [readTapeBit IN i])) := by
  simp [step, raw, acfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end]

theorem endA_step (i y : ℕ) (IN S R Z : List Bool) (h : readTapeBit IN i = false) :
    step raw (acfg 0 i y IN S R Z) = some (acfg 2 i y IN S R Z) := by
  simp [step, raw, acfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem markB_step (i y : ℕ) (IN S R Z : List Bool) (h : readTapeBit R y = true) :
    step raw (acfg 2 i y IN S R Z) = some (acfg 3 i y IN S R (Z ++ [true])) := by
  simp [step, raw, acfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end]

theorem bitB_step (i y : ℕ) (IN S R Z : List Bool) :
    step raw (acfg 3 i y IN S R Z) = some (acfg 2 i (y + 1) IN S R (Z ++ [readTapeBit S y])) := by
  simp [step, raw, acfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end]

theorem endB_step (i y : ℕ) (IN S R Z : List Bool) (h : readTapeBit R y = false) :
    step raw (acfg 2 i y IN S R Z) = some (acfg 4 i y IN S R (Z ++ [false])) := by
  simp [step, raw, acfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end]

/-- Phase A: the marks of the framed request are copied. -/
theorem loopA (IN S R : List Bool) (v : List Bool) :
    ∀ (u Z : List Bool), IN = Streaming.marks u ++ frame v →
      Timed raw (2 * v.length) (acfg 0 (2 * u.length) 0 IN S R Z)
        (acfg 0 (2 * (u.length + v.length)) 0 IN S R (Z ++ Streaming.marks v)) := by
  induction v with
  | nil => intro u Z _; simpa [Streaming.marks] using Timed.refl raw (acfg 0 (2 * u.length) 0 IN S R Z)
  | cons b v ih =>
    intro u Z hIN
    have hr1 : readTapeBit IN (2 * u.length) = true := by
      rw [hIN, frame_cons, ← Streaming.marks_length]
      exact Streaming.read_append _ _ _
    have hr2 : readTapeBit IN (2 * u.length + 1) = b := by
      rw [hIN, frame_cons, ← Streaming.marks_length]
      have h := Streaming.read_append (Streaming.marks u ++ [true]) (frame v) b
      simpa using h
    have h1 := Timed.single (p := raw) (by rfl) (markA_step (2 * u.length) 0 IN S R Z hr1)
    have h2 := Timed.single (p := raw) (by rfl) (bitA_step (2 * u.length + 1) 0 IN S R (Z ++ [true]))
    rw [hr2] at h2
    have hIN' : IN = Streaming.marks (u ++ [b]) ++ frame v := by
      rw [hIN, Streaming.marks_append, frame_cons]; simp [Streaming.marks]
    have h3 := ih (u ++ [b]) (Z ++ [true] ++ [b]) hIN'
    rw [show 2 * (u ++ [b]).length = 2 * u.length + 1 + 1 by simp; ring] at h3
    have h := (h1.trans h2).trans h3
    have e1 : 1 + 1 + 2 * v.length = 2 * (b :: v).length := by simp; ring
    have e2 : 2 * ((u ++ [b]).length + v.length) = 2 * (u.length + (b :: v).length) := by simp; ring
    have e3 : Z ++ [true] ++ [b] ++ Streaming.marks v = Z ++ Streaming.marks (b :: v) := by simp [Streaming.marks]
    rw [e1, e2, e3] at h
    exact h

/-- Phase B: the raw output is framed, driven by its ruler. -/
theorem loopB (i : ℕ) (IN S : List Bool) (post : List Bool) :
    ∀ (pre Z : List Bool), S = pre ++ post →
      Timed raw (2 * post.length) (acfg 2 i pre.length IN S (List.replicate S.length true) Z)
        (acfg 2 i S.length IN S (List.replicate S.length true) (Z ++ Streaming.marks post)) := by
  induction post with
  | nil =>
    intro pre Z hS
    subst hS
    simpa [Streaming.marks] using Timed.refl raw (acfg 2 i pre.length IN pre (List.replicate pre.length true) Z)
  | cons c post ih =>
    intro pre Z hS
    have hlen : pre.length < S.length := by rw [hS]; simp
    have hr1 : readTapeBit (List.replicate S.length true) pre.length = true := read_replicate_true _ _ hlen
    have hr2 : readTapeBit S pre.length = c := by rw [hS]; exact Streaming.read_append _ _ _
    have h1 := Timed.single (p := raw) (by rfl)
      (markB_step i pre.length IN S (List.replicate S.length true) Z hr1)
    have h2 := Timed.single (p := raw) (by rfl)
      (bitB_step i pre.length IN S (List.replicate S.length true) (Z ++ [true]))
    rw [hr2] at h2
    have h3 := ih (pre ++ [c]) (Z ++ [true] ++ [c]) (by rw [hS]; simp)
    rw [show (pre ++ [c]).length = pre.length + 1 by simp] at h3
    have h := (h1.trans h2).trans h3
    have e1 : 1 + 1 + 2 * post.length = 2 * (c :: post).length := by simp; ring
    have e3 : Z ++ [true] ++ [c] ++ Streaming.marks post = Z ++ Streaming.marks (c :: post) := by
      simp [Streaming.marks]
    rw [e1, e3] at h
    exact h

theorem frame_eq (w s : List Bool) : frame (w ++ s) = Streaming.marks w ++ Streaming.marks s ++ [false] := by
  rw [← Streaming.marks_append, show w ++ s = (w ++ s) ++ [] by simp, Streaming.frame_append]
  simp [frame]

theorem raw_run (w s : List Bool) : ∃ r : ExecutionReceipt 4 5,
    run raw (2 * w.length + 2 * s.length + 2) ![frame w, s, List.replicate s.length true, []] = some r ∧
      r.final.tapes = ![frame w, s, List.replicate s.length true, frame (w ++ s)] ∧
      r.steps = 2 * w.length + 2 * s.length + 2 := by
  set R := List.replicate s.length true with hR
  have hA := loopA (frame w) s R w [] [] (by simp [Streaming.marks])
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.nil_append] at hA
  have hend : readTapeBit (frame w) (2 * w.length) = false := by
    have e : frame w = Streaming.marks w ++ false :: [] := by
      have := Streaming.frame_append w []
      simpa [frame] using this
    rw [e, ← Streaming.marks_length]
    exact Streaming.read_append _ _ _
  have h2 := Timed.single (p := raw) (by rfl) (endA_step (2 * w.length) 0 (frame w) s R (Streaming.marks w) hend)
  have hB := loopB (2 * w.length) (frame w) s s [] (Streaming.marks w) (by simp)
  simp only [List.length_nil] at hB
  have h4 := Timed.single (p := raw) (by rfl)
    (endB_step (2 * w.length) s.length (frame w) s R (Streaming.marks w ++ Streaming.marks s)
      (read_replicate_end s.length true))
  have h := ((hA.trans h2).trans hB).trans h4
  obtain ⟨r, hr, hf, hs⟩ := h.run rfl
  have hinit : acfg 0 0 0 (frame w) s R [] = initialConfiguration raw ![frame w, s, R, []] := by
    apply configuration_ext
    · rfl
    · funext k; fin_cases k <;> rfl
    · rfl
  rw [hinit] at hr
  refine ⟨r, ?_, ?_, ?_⟩
  · have e : 2 * w.length + 1 + 2 * s.length + 1 = 2 * w.length + 2 * s.length + 2 := by ring
    rw [e] at hr
    exact hr
  · rw [hf, frame_eq]
    rfl
  · rw [hs]; ring

/-- **The append stage**: from `frame w`, the raw `s` and its ruler (heads at `0`), the kernel under base `Rewind`
writes `frame (w ++ s)` on tape `3`; all heads end at `0`. -/
theorem append_step (w s : List Bool) : ∃ tout : Fin (4 + 1) → List Bool,
    Step (Rewind.machine raw) (4 * w.length + 4 * s.length + 6) (fun _ => 0)
      (Fin.addCases ![frame w, s, List.replicate s.length true, []] (fun _ => [])) (fun _ => 0) tout ∧
      tout 3 = frame (w ++ s) := by
  obtain ⟨src, hsrc, hf, hs⟩ := raw_run w s
  obtain ⟨r, hr, htapes, _, hheads, hsteps, _⟩ := Rewind.Workspace.reset_workspace raw _ _ src hsrc 0
  refine ⟨r.final.tapes, ⟨r, ?_, funext hheads, rfl, ?_⟩, ?_⟩
  · have e : 2 * src.steps + 2 = 4 * w.length + 4 * s.length + 6 := by rw [hs]; ring
    rw [e] at hr
    exact hr
  · rw [hsteps, hs]; omega
  · have h3 := htapes 3
    rw [hf] at h3
    exact h3

end NearCubicWires.WireExponent3_5.PrimAsm.AppendFrame
