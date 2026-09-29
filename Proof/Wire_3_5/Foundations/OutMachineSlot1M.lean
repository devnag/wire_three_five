import Proof.Wire_3_5.Foundations.OutMachineSlot1W

/-! # SA's slot 1, part 2: copying frames out of the framed input

The final pass's input stream holds `frame (fpIn r)`: every bit of `fpIn` behind a mark (`marks`). The seed's frames
inside it are read through the marks and written raw (`CarWM.copyFrameW` is the raw-input twin):

* `copyBodyM`, **`copyLoopM_spec`**, **`copyFrameM`**, **`copyFrameM_spec`**: one frame copied to the end of `X`;
* **`countLoop`**, **`countLoop_spec`**: every frame up to the input's end marker copied to `X`, their number counted;
* **`copyLoopN`**, **`copyLoopN_spec`**: the first `k` frames copied to `X`.

Paper quantity of the main type: the seed's frames of the final pass's input (P3:3165-3175). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Slot1
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.PrimT.CarWM (rd_at rd_at1)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)

section Copy
variable {ns nr : ℕ} (cap : ℕ)

/-- One marked pair of a frame copied raw to the end of `X` (the head on the pair's first bit's value cell). -/
def copyBodyM (I X : Fin (ns + 1)) : WM ns nr :=
  .seq (emitW X true) (.seq (.fwd I) (.seq (.fwd I) (.seq (.ifs I (emitW X true) (emitW X false))
    (.seq (.fwd I) (.fwd I)))))

theorem rd_at3 (pre l : List Bool) : readTapeBit (pre ++ l) (pre.length + 3) = l.getD 3 false := by
  unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (by omega)]; simp

theorem copyLoopM_spec (I X : Fin (ns + 1)) (hIX : I ≠ X) (rest : List Bool) :
    ∀ (y pre : List Bool) (σ : WState ns nr), σ.st I = pre ++ (marks (frame y) ++ rest) →
      σ.sh I = pre.length + 1 → σ.sh X = (σ.st X).length →
      ∃ τ, WExec cap (.whs I (copyBodyM I X)) σ τ (18 * y.length + 1) ∧ τ.st X = σ.st X ++ frameP y ∧
        τ.sh X = (τ.st X).length ∧ τ.st I = σ.st I ∧ τ.sh I = pre.length + 1 + 4 * y.length ∧
        (∀ j, j ≠ I → j ≠ X → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], pre, σ, hI, hIh, hX => by
    have hz : wbit σ I = false := by simp only [wbit, hI, hIh, rd_at1]; rfl
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp [frameP], hX, rfl, by simp [hIh],
      fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | b :: bs, pre, σ, hI, hIh, hX => by
    have hXI : X ≠ I := fun e => hIX e.symm
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap X true σ hX
    have I1 := o1 I hIX
    obtain ⟨σ2, s2, n2, n2h, o2, v2, c2⟩ := fwd_facts cap I σ1
    have X2 := o2 X hXI
    obtain ⟨σ3, s3, n3, n3h, o3, v3, c3⟩ := fwd_facts cap I σ2
    have X3 := o3 X hXI
    have hb : wbit σ3 I = b := by
      simp only [wbit, n3, n3h, n2, n2h, I1.1, I1.2, hI, hIh]
      rw [show pre.length + 1 + 1 + 1 = pre.length + 3 by omega, rd_at3]
      simp [frame, marks]
    obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := emit_facts cap X b σ3 (by rw [X3.1, X3.2, X2.1, X2.2, e1h])
    have s4' : WExec cap (.ifs I (emitW X true) (emitW X false)) σ3 σ4 4 := by
      cases b
      · exact WExec.ifsF hb s4
      · exact WExec.ifsT hb s4
    have I4 := o4 I hIX
    obtain ⟨σ5, s5, n5, n5h, o5, v5, c5⟩ := fwd_facts cap I σ4
    have X5 := o5 X hXI
    obtain ⟨σ6, s6, n6, n6h, o6, v6, c6⟩ := fwd_facts cap I σ5
    have X6 := o6 X hXI
    obtain ⟨τ, s7, eX, eXh, eI, eIh, oth, v7, c7⟩ := copyLoopM_spec I X hIX rest bs (pre ++ [true, true, true, b]) σ6
      (by rw [n6, n5, I4.1, n3, n2, I1.1, hI]; simp [frame, marks])
      (by rw [n6h, n5h, I4.2, n3h, n2h, I1.2, hIh]; simp)
      (by rw [X6.1, X6.2, X5.1, X5.2, e4h])
    have hw : wbit σ I = true := by
      simp only [wbit, hI, hIh, rd_at1]; simp [frame, marks]
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4'
      (WExec.seq s5 s6))))) s7) (by simp; omega), ?_, eXh, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eX, X6.1, X5.1, e4, X3.1, X2.1, e1]; simp [frameP]
    · rw [eI, n6, n5, I4.1, n3, n2, I1.1]
    · rw [eIh]; simp; omega
    · intro j h1 h2
      exact (((((o1 j h2).trans' (o2 j h1)).trans' (o3 j h1)).trans' (o4 j h2)).trans' ((o5 j h1).trans'
        (o6 j h1))).trans' (oth j h1 h2)
    · rw [v7, v6, v5, v4, v3, v2, v1]
    · rw [c7, c6, c5, c4, c3, c2, c1]

/-- **One framed word copied** from the marked input `I` (at its head) to the end of `X`. -/
def copyFrameM (I X : Fin (ns + 1)) : WM ns nr :=
  .seq (.fwd I) (.seq (.whs I (copyBodyM I X)) (.seq (emitW X false) (.fwd I)))

theorem copyFrameM_spec (I X : Fin (ns + 1)) (hIX : I ≠ X) (pre y rest : List Bool) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (marks (frame y) ++ rest)) (hIh : σ.sh I = pre.length) (hX : σ.sh X = (σ.st X).length) :
    ∃ τ, WExec cap (copyFrameM I X) σ τ (18 * y.length + 9) ∧ τ.st X = σ.st X ++ frame y ∧
      τ.sh X = (τ.st X).length ∧ τ.st I = σ.st I ∧ τ.sh I = pre.length + (marks (frame y)).length ∧
      (∀ j, j ≠ I → j ≠ X → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hXI : X ≠ I := fun e => hIX e.symm
  obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := fwd_facts cap I σ
  have X1 := o1 X hXI
  obtain ⟨σ2, s2, e2, e2h, n2, n2h, o2, v2, c2⟩ := copyLoopM_spec cap I X hIX rest y pre σ1 (by rw [n1, hI])
    (by rw [n1h, hIh]) (by rw [X1.1, X1.2, hX])
  obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap X false σ2 e2h
  have I3 := o3 I hIX
  obtain ⟨τ, s4, n4, n4h, o4, v4, c4⟩ := fwd_facts cap I σ3
  have X4 := o4 X hXI
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [X4.1, e3, e2, X1.1, frame_eq_frameP]; simp
  · rw [X4.1, X4.2, e3h]
  · rw [n4, I3.1, n2, n1]
  · rw [n4h, I3.2, n2h, marks_length]
    have : (frame y).length = 2 * y.length + 1 := by rw [frame_eq_frameP]; simp [frameP]; ring
    rw [this]; omega
  · intro j h1 h2
    exact (((o1 j h1).trans' (o2 j h1 h2)).trans' (o3 j h2)).trans' (o4 j h1)
  · rw [v4, v3, v2, v1]
  · rw [c4, c3, c2, c1]

/-- **Every frame up to the input's end marker** copied to `X`, their number added to `C`. -/
def countLoop (I X : Fin (ns + 1)) (C : Fin nr) : WM ns nr := .whs I (.seq (copyFrameM I X) (.inc C))

theorem frame_length (y : List Bool) : (frame y).length = 2 * y.length + 1 := by
  rw [frame_eq_frameP]; simp [frameP]; ring

theorem countLoop_spec (I X : Fin (ns + 1)) (hIX : I ≠ X) (C : Fin nr) (rest : List Bool) :
    ∀ (ys : List (List Bool)) (pre : List Bool) (σ : WState ns nr),
      σ.st I = pre ++ (marks ((ys.map frame).flatten) ++ false :: rest) → σ.sh I = pre.length →
      σ.sh X = (σ.st X).length → σ.val C + ys.length ≤ cap →
      ∃ τ, WExec cap (countLoop I X C) σ τ (15 * ((ys.map frame).flatten).length + 1) ∧
        τ.st X = σ.st X ++ (ys.map frame).flatten ∧ τ.sh X = (τ.st X).length ∧ τ.st I = σ.st I ∧
        τ.sh I = pre.length + (marks ((ys.map frame).flatten)).length ∧
        (∀ j, j ≠ I → j ≠ X → Same σ τ j) ∧ τ.val = Function.update σ.val C (σ.val C + ys.length) ∧
        τ.cell = σ.cell
  | [], pre, σ, hI, hIh, hX, _ => by
    have hz : wbit σ I = false := by simp only [wbit, hI, hIh, rd_at]; simp
    refine ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hX, rfl, by simp [hIh],
      fun _ _ _ => ⟨rfl, rfl⟩, ?_, rfl⟩
    simp
  | y :: ys, pre, σ, hI, hIh, hX, hC => by
    obtain ⟨σ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := copyFrameM_spec cap I X hIX pre y
      (marks ((ys.map frame).flatten) ++ false :: rest) σ
      (by rw [hI]; simp [marks_append, List.append_assoc]) hIh hX
    have s2 := WExec.inc (cap := cap) C σ1 (by rw [v1]; simp at hC; omega)
    obtain ⟨τ, s3, e3, e3h, n3, n3h, o3, v3, c3⟩ := countLoop_spec I X hIX C rest ys (pre ++ marks (frame y))
      (σ1.setv C (σ1.val C + 1)) (by simp only [WState.setv_st]; rw [n1, hI]; simp [marks_append, List.append_assoc])
      (by simp only [WState.setv_sh]; rw [n1h]; simp) (by simp only [WState.setv_sh, WState.setv_st]; exact e1h)
      (by simp only [WState.setv_val, Function.update_self]; rw [v1]; simp at hC; omega)
    have hw : wbit σ I = true := by
      simp only [wbit, hI, hIh, rd_at]; simp [frame, marks]
      cases y <;> simp [frame, marks]
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, ?_, e3h, ?_, ?_, ?_, ?_, ?_⟩
    · have := frame_length y
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      omega
    · rw [e3]; simp only [WState.setv_st]; rw [e1]; simp
    · rw [n3]; simp only [WState.setv_st]; exact n1
    · rw [n3h]; simp [marks_append]; omega
    · intro j h1 h2
      exact ((o1 j h1 h2).trans' ⟨rfl, rfl⟩).trans' (o3 j h1 h2)
    · rw [v3]
      funext q
      simp only [WState.setv_val, Function.update_apply, v1]
      split_ifs <;> simp_all <;> omega
    · rw [c3]; simp only [WState.setv_cell]; exact c1

/-- **The first `k` frames** copied to `X` (`C = k` counted down). -/
def copyLoopN (I X : Fin (ns + 1)) (C : Fin nr) : WM ns nr := .whr C (.seq (.dec C) (copyFrameM I X))

theorem copyLoopN_spec (I X : Fin (ns + 1)) (hIX : I ≠ X) (C : Fin nr) (rest : List Bool) :
    ∀ (k : ℕ) (ys : List (List Bool)) (pre : List Bool) (σ : WState ns nr), k ≤ ys.length →
      σ.st I = pre ++ (marks ((ys.map frame).flatten) ++ rest) → σ.sh I = pre.length →
      σ.sh X = (σ.st X).length → σ.val C = k → k ≤ cap →
      ∃ τ, WExec cap (copyLoopN I X C) σ τ (15 * (((ys.take k).map frame).flatten).length + 1) ∧
        τ.st X = σ.st X ++ ((ys.take k).map frame).flatten ∧ τ.sh X = (τ.st X).length ∧ τ.st I = σ.st I ∧
        τ.sh I = pre.length + (marks (((ys.take k).map frame).flatten)).length ∧
        (∀ j, j ≠ I → j ≠ X → Same σ τ j) ∧ τ.val = Function.update σ.val C 0 ∧ τ.cell = σ.cell
  | 0, ys, pre, σ, _, _, hIh, hX, hC, _ => by
    refine ⟨σ, WExec.mono (WExec.whrF hC) (by omega), by simp, hX, rfl, by simp [hIh],
      fun _ _ _ => ⟨rfl, rfl⟩, ?_, rfl⟩
    funext q; simp only [Function.update_apply]; split_ifs with h
    · subst h; exact hC
    · rfl
  | k + 1, [], _, _, hk, _, _, _, _, _ => by simp at hk
  | k + 1, y :: ys, pre, σ, hk, hI, hIh, hX, hC, hcap => by
    have s1 := WExec.dec (cap := cap) C σ (by omega)
    obtain ⟨σ2, s2, e2, e2h, n2, n2h, o2, v2, c2⟩ := copyFrameM_spec cap I X hIX pre y
      (marks ((ys.map frame).flatten) ++ rest) (σ.setv C (σ.val C - 1))
      (by simp only [WState.setv_st]; rw [hI]; simp [marks_append, List.append_assoc])
      (by simp only [WState.setv_sh]; exact hIh) (by simp only [WState.setv_sh, WState.setv_st]; exact hX)
    obtain ⟨τ, s3, e3, e3h, n3, n3h, o3, v3, c3⟩ := copyLoopN_spec I X hIX C rest k ys (pre ++ marks (frame y)) σ2
      (by simp at hk; omega) (by rw [n2]; simp only [WState.setv_st]; rw [hI]; simp [marks_append, List.append_assoc])
      (by rw [n2h]; simp) e2h (by rw [v2]; simp [hC]) (by omega)
    have hne : σ.val C ≠ 0 := by rw [hC]; omega
    refine ⟨τ, WExec.mono (WExec.whrT hne (WExec.seq s1 s2) s3) ?_, ?_, e3h, ?_, ?_, ?_, ?_, ?_⟩
    · have := frame_length y
      simp only [List.take_succ_cons, List.map_cons, List.flatten_cons, List.length_append]
      omega
    · rw [e3, e2]; simp only [WState.setv_st]; simp
    · rw [n3, n2]; rfl
    · rw [n3h]; simp [marks_append]; omega
    · intro j h1 h2
      exact Same.trans' (⟨rfl, rfl⟩ : Same σ (σ.setv C (σ.val C - 1)) j) ((o2 j h1 h2).trans' (o3 j h1 h2))
    · rw [v3, v2]; funext q; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> rfl
    · rw [c3, c2]; rfl

end Copy

end NearCubicWires.WireExponent3_5.FinalPass.Out.Slot1
