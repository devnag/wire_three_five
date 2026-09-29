import Proof.Wire_3_5.UnionMachine.CWParCnt

/-! # C6 front, U5, the code writers: the parity's field lists from the support bitmap

The encoding parity of a systematic variable with support `S` (P3:3092-3094; `unionParityAtom`) has the
bottoms `thresholdParityBottomGate S j`: weights `[i ∈ S]`, threshold `j + 1`, support `S`. Their codes carry the
balanced lists `encodeIntList` of the weights (atoms `encodeInt 1 = 9`, `encodeInt 0 = 0`) and `encodeBoolList` of the
support, which base's serializer writes from framed fields. From the bitmap `frame (bitmap S)` this word program writes,
in one pass:
* the weights' fields `wlF l` (`[t,f,f,t]` = 9 or `[f]` = 0 per bit) and the support's fields `sgl l`;
* the count words `false :: 1^q` and `false :: 1^k`, `k = |S|`.

Paper quantity of the main type (**`genB_spec`**): the atoms of the parity bottoms' weight list and support list. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParGen
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt (sgl sgl_cons sgl_append)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

section Emit
variable {ns nr : ℕ} (cap : ℕ)

/-- Append a fixed word. -/
def emitL (o : Fin (ns + 1)) : List Bool → WM ns nr
  | [] => .skip
  | b :: w => .seq (emitW o b) (emitL o w)

theorem emitL_spec (o : Fin (ns + 1)) :
    ∀ (w : List Bool) (σ : WState ns nr), σ.sh o = (σ.st o).length →
      ∃ τ, WExec cap (emitL o w) σ τ (4 * w.length) ∧ τ.st o = σ.st o ++ w ∧ τ.sh o = (τ.st o).length ∧
        (∀ j, j ≠ o → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], σ, ho => ⟨σ, WExec.skip σ, by simp, ho, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | b :: w, σ, ho => by
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap o b σ ho
    obtain ⟨τ, s2, e2, e2h, o2, v2, c2⟩ := emitL_spec o w σ1 e1h
    refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by simp; omega), by rw [e2, e1]; simp, e2h,
      fun j hj => (o1 j hj).trans' (o2 j hj), by rw [v2, v1], by rw [c2, c1]⟩

end Emit

/-! ## The base fields -/

/-- The code of the weight `1` (`encodeInt 1 = 9`), least significant bit first. -/
def w9 : List Bool := [true, false, false, true]

/-- The weights' fields: `9` for a member, `0` for a non-member. -/
def wlF (l : List Bool) : List Bool := (l.map fun b => if b then w9 else [false]).flatMap frame

theorem wlF_cons (b : Bool) (l : List Bool) : wlF (b :: l) = frame (if b then w9 else [false]) ++ wlF l := rfl

/-- One bitmap bit: to its fields and counts (streams `0` the bitmap, `1` the weights' fields, `2` the support's
fields, `3` the count `q`, `4` the count `k`). -/
def gBody : WM 4 0 :=
  .seq (.fwd 0) (.seq (.ifs 0
    (.seq (emitL 1 (frame w9)) (.seq (emitL 2 [true, true, false]) (.seq (emitW 3 true) (emitW 4 true))))
    (.seq (emitL 1 (frame [false])) (.seq (emitL 2 [true, false, false]) (emitW 3 true)))) (.fwd 0))

/-- **The base fields' pass.** -/
def genB : WM 4 0 := .seq (emitW 3 false) (.seq (emitW 4 false) (.whs 0 gBody))

/-- The stream facts of the pass, stream by stream. -/
structure GenOut (σ τ : WState 4 0) (l : List Bool) : Prop where
  s0 : τ.st 0 = σ.st 0
  s1 : τ.st 1 = σ.st 1 ++ wlF l
  h1 : τ.sh 1 = (τ.st 1).length
  s2 : τ.st 2 = σ.st 2 ++ sgl l
  h2 : τ.sh 2 = (τ.st 2).length
  s3 : τ.st 3 = σ.st 3 ++ List.replicate l.length true
  h3 : τ.sh 3 = (τ.st 3).length
  s4 : τ.st 4 = σ.st 4 ++ List.replicate (l.count true) true
  h4 : τ.sh 4 = (τ.st 4).length
  c : τ.cell = σ.cell

/-- One bit of the pass, from its pair's marker to the next pair's marker. -/
theorem gBody_spec (cap : ℕ) (b : Bool) (l pre : List Bool) (σ : WState 4 0) (h0 : σ.st 0 = pre ++ frame (b :: l))
    (h0h : σ.sh 0 = pre.length) (h1 : σ.sh 1 = (σ.st 1).length) (h2 : σ.sh 2 = (σ.st 2).length)
    (h3 : σ.sh 3 = (σ.st 3).length) (h4 : σ.sh 4 = (σ.st 4).length) :
    ∃ τ, WExec cap gBody σ τ 70 ∧ GenOut σ τ [b] ∧ τ.sh 0 = pre.length + 2 := by
  obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap (0 : Fin 5) σ
  have hbit : wbit σ1 0 = b := by
    unfold wbit; rw [a1, a1h, h0, h0h]; unfold readTapeBit; simp [frame]
  have hs : ∀ j : Fin 5, j ≠ 0 → σ1.st j = σ.st j ∧ σ1.sh j = σ.sh j := fun j hj => ⟨(o1 j hj).1, (o1 j hj).2⟩
  -- the branch
  have hbr : ∃ σ2, WExec cap (.ifs 0
      (.seq (emitL 1 (frame w9)) (.seq (emitL 2 [true, true, false]) (.seq (emitW 3 true) (emitW 4 true))))
      (.seq (emitL 1 (frame [false])) (.seq (emitL 2 [true, false, false]) (emitW 3 true)))) σ1 σ2 64 ∧
      GenOut σ1 σ2 [b] ∧ σ2.sh 0 = σ1.sh 0 := by
    cases hb : b
    · rw [hb] at hbit
      obtain ⟨τa, sa, ea, eah, oa, va, ca⟩ := emitL_spec cap (1 : Fin 5) (frame [false]) σ1
        (by rw [(hs 1 (by decide)).1, (hs 1 (by decide)).2, h1])
      obtain ⟨τb, sb, eb, ebh, ob, vb, cb⟩ := emitL_spec cap (2 : Fin 5) [true, false, false] τa
        (by rw [(oa 2 (by decide)).1, (oa 2 (by decide)).2, (hs 2 (by decide)).1, (hs 2 (by decide)).2, h2])
      obtain ⟨τc, sc, ec, ech, oc, vc, cc⟩ := emit_facts cap (3 : Fin 5) true τb
        (by rw [(ob 3 (by decide)).1, (ob 3 (by decide)).2, (oa 3 (by decide)).1, (oa 3 (by decide)).2,
          (hs 3 (by decide)).1, (hs 3 (by decide)).2, h3])
      refine ⟨τc, WExec.mono (WExec.ifsF hbit (WExec.seq sa (WExec.seq sb sc))) (by simp [frame]), ⟨?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [(oc 0 (by decide)).1, (ob 0 (by decide)).1, (oa 0 (by decide)).1]
      · rw [(oc 1 (by decide)).1, (ob 1 (by decide)).1, ea]; rfl
      · rw [(oc 1 (by decide)).2, (ob 1 (by decide)).2, eah, (oc 1 (by decide)).1, (ob 1 (by decide)).1]
      · rw [(oc 2 (by decide)).1, eb, (oa 2 (by decide)).1]; rfl
      · rw [(oc 2 (by decide)).2, ebh, (oc 2 (by decide)).1]
      · rw [ec, (ob 3 (by decide)).1, (oa 3 (by decide)).1]; rfl
      · exact ech
      · rw [(oc 4 (by decide)).1, (ob 4 (by decide)).1, (oa 4 (by decide)).1]; simp
      · rw [(oc 4 (by decide)).2, (ob 4 (by decide)).2, (oa 4 (by decide)).2, (oc 4 (by decide)).1,
          (ob 4 (by decide)).1, (oa 4 (by decide)).1, (hs 4 (by decide)).1, (hs 4 (by decide)).2, h4]
      · rw [cc, cb, ca]
      · rw [(oc 0 (by decide)).2, (ob 0 (by decide)).2, (oa 0 (by decide)).2]
    · rw [hb] at hbit
      obtain ⟨τa, sa, ea, eah, oa, va, ca⟩ := emitL_spec cap (1 : Fin 5) (frame w9) σ1
        (by rw [(hs 1 (by decide)).1, (hs 1 (by decide)).2, h1])
      obtain ⟨τb, sb, eb, ebh, ob, vb, cb⟩ := emitL_spec cap (2 : Fin 5) [true, true, false] τa
        (by rw [(oa 2 (by decide)).1, (oa 2 (by decide)).2, (hs 2 (by decide)).1, (hs 2 (by decide)).2, h2])
      obtain ⟨τc, sc, ec, ech, oc, vc, cc⟩ := emit_facts cap (3 : Fin 5) true τb
        (by rw [(ob 3 (by decide)).1, (ob 3 (by decide)).2, (oa 3 (by decide)).1, (oa 3 (by decide)).2,
          (hs 3 (by decide)).1, (hs 3 (by decide)).2, h3])
      obtain ⟨τd, sd, ed, edh, od, vd, cd⟩ := emit_facts cap (4 : Fin 5) true τc
        (by rw [(oc 4 (by decide)).1, (oc 4 (by decide)).2, (ob 4 (by decide)).1, (ob 4 (by decide)).2,
          (oa 4 (by decide)).1, (oa 4 (by decide)).2, (hs 4 (by decide)).1, (hs 4 (by decide)).2, h4])
      refine ⟨τd, WExec.mono (WExec.ifsT hbit (WExec.seq sa (WExec.seq sb (WExec.seq sc sd)))) (by simp [frame, w9]),
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [(od 0 (by decide)).1, (oc 0 (by decide)).1, (ob 0 (by decide)).1, (oa 0 (by decide)).1]
      · rw [(od 1 (by decide)).1, (oc 1 (by decide)).1, (ob 1 (by decide)).1, ea]; rfl
      · rw [(od 1 (by decide)).2, (oc 1 (by decide)).2, (ob 1 (by decide)).2, eah, (od 1 (by decide)).1,
          (oc 1 (by decide)).1, (ob 1 (by decide)).1]
      · rw [(od 2 (by decide)).1, (oc 2 (by decide)).1, eb, (oa 2 (by decide)).1]; rfl
      · rw [(od 2 (by decide)).2, (oc 2 (by decide)).2, ebh, (od 2 (by decide)).1, (oc 2 (by decide)).1]
      · rw [(od 3 (by decide)).1, ec, (ob 3 (by decide)).1, (oa 3 (by decide)).1]; rfl
      · rw [(od 3 (by decide)).2, ech, (od 3 (by decide)).1]
      · rw [ed, (oc 4 (by decide)).1, (ob 4 (by decide)).1, (oa 4 (by decide)).1]; rfl
      · exact edh
      · rw [cd, cc, cb, ca]
      · rw [(od 0 (by decide)).2, (oc 0 (by decide)).2, (ob 0 (by decide)).2, (oa 0 (by decide)).2]
  obtain ⟨σ2, s2, g2, e2h⟩ := hbr
  obtain ⟨τ, s3, a3, a3h, o3, v3, c3⟩ := fwd_facts cap (0 : Fin 5) σ2
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [a3, g2.s0, a1]
  · rw [(o3 1 (by decide)).1, g2.s1, (hs 1 (by decide)).1]
  · rw [(o3 1 (by decide)).2, g2.h1, (o3 1 (by decide)).1]
  · rw [(o3 2 (by decide)).1, g2.s2, (hs 2 (by decide)).1]
  · rw [(o3 2 (by decide)).2, g2.h2, (o3 2 (by decide)).1]
  · rw [(o3 3 (by decide)).1, g2.s3, (hs 3 (by decide)).1]
  · rw [(o3 3 (by decide)).2, g2.h3, (o3 3 (by decide)).1]
  · rw [(o3 4 (by decide)).1, g2.s4, (hs 4 (by decide)).1]
  · rw [(o3 4 (by decide)).2, g2.h4, (o3 4 (by decide)).1]
  · rw [c3, g2.c, c1]
  · rw [a3h, e2h, a1h, h0h]

theorem wlF_append (l l' : List Bool) : wlF (l ++ l') = wlF l ++ wlF l' := by
  unfold wlF; rw [List.map_append, List.flatMap_append]

theorem GenOut.refl (σ : WState 4 0) (h1 : σ.sh 1 = (σ.st 1).length) (h2 : σ.sh 2 = (σ.st 2).length)
    (h3 : σ.sh 3 = (σ.st 3).length) (h4 : σ.sh 4 = (σ.st 4).length) : GenOut σ σ [] :=
  ⟨rfl, by simp [wlF], h1, by simp [sgl], h2, by simp, h3, by simp, h4, rfl⟩

theorem GenOut.trans {σ σ1 τ : WState 4 0} {l1 l2 : List Bool} (g1 : GenOut σ σ1 l1) (g2 : GenOut σ1 τ l2) :
    GenOut σ τ (l1 ++ l2) :=
  ⟨by rw [g2.s0, g1.s0], by rw [g2.s1, g1.s1, wlF_append, List.append_assoc], g2.h1,
    by rw [g2.s2, g1.s2, sgl_append, List.append_assoc], g2.h2,
    by rw [g2.s3, g1.s3, List.length_append, List.replicate_add, List.append_assoc], g2.h3,
    by rw [g2.s4, g1.s4, List.count_append, List.replicate_add, List.append_assoc], g2.h4,
    by rw [g2.c, g1.c]⟩

/-- **The pass's loop**: every bitmap bit. -/
theorem gLoop_spec (cap : ℕ) : ∀ (l pre : List Bool) (σ : WState 4 0), σ.st 0 = pre ++ frame l →
    σ.sh 0 = pre.length → σ.sh 1 = (σ.st 1).length → σ.sh 2 = (σ.st 2).length → σ.sh 3 = (σ.st 3).length →
    σ.sh 4 = (σ.st 4).length →
    ∃ τ, WExec cap (.whs 0 gBody) σ τ (72 * l.length + 1) ∧ GenOut σ τ l
  | [], pre, σ, h0, h0h, h1, h2, h3, h4 => by
    have hz : wbit σ 0 = false := by unfold wbit; rw [h0, h0h]; unfold readTapeBit; simp [frame]
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), GenOut.refl σ h1 h2 h3 h4⟩
  | b :: l, pre, σ, h0, h0h, h1, h2, h3, h4 => by
    have hr : wbit σ 0 = true := by unfold wbit; rw [h0, h0h]; unfold readTapeBit; simp [frame]
    obtain ⟨σ1, s1, g1, e1h⟩ := gBody_spec cap b l pre σ h0 h0h h1 h2 h3 h4
    obtain ⟨τ, s2, g2⟩ := gLoop_spec cap l (pre ++ [true, b]) σ1
      (by rw [g1.s0, h0]; simp [frame]) (by rw [e1h]; simp) g1.h1 g1.h2 g1.h3 g1.h4
    exact ⟨τ, WExec.mono (WExec.whsT hr s1 s2) (by simp; ring_nf; omega), g1.trans g2⟩

/-- **The base fields' pass**: from the bitmap, the weights' fields, the support's fields and both counts. -/
theorem genB_spec (cap : ℕ) (l : List Bool) (σ : WState 4 0) (h0 : ∀ j, σ.sh j = 0) (hB : σ.st 0 = frame l)
    (hE : ∀ j : Fin 5, j ≠ 0 → σ.st j = []) :
    ∃ τ, WExec cap genB σ τ (72 * l.length + 9) ∧ τ.st 0 = frame l ∧ τ.st 1 = wlF l ∧ τ.st 2 = sgl l ∧
      τ.st 3 = CompareMachine.word l.length ∧ τ.st 4 = CompareMachine.word (l.count true) ∧ τ.cell = σ.cell := by
  obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (3 : Fin 5) false σ (by rw [h0, hE 3 (by decide)]; rfl)
  obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap (4 : Fin 5) false σ1
    (by rw [(o1 4 (by decide)).1, (o1 4 (by decide)).2, h0, hE 4 (by decide)]; rfl)
  have S2 : ∀ j : Fin 5, j ≠ 3 → j ≠ 4 → σ2.st j = σ.st j ∧ σ2.sh j = σ.sh j := fun j h3 h4 =>
    ⟨((o1 j h3).trans' (o2 j h4)).1, ((o1 j h3).trans' (o2 j h4)).2⟩
  obtain ⟨τ, s3, g⟩ := gLoop_spec cap l [] σ2 (by rw [(S2 0 (by decide) (by decide)).1, hB]; rfl)
    (by rw [(S2 0 (by decide) (by decide)).2, h0]; rfl)
    (by rw [(S2 1 (by decide) (by decide)).1, (S2 1 (by decide) (by decide)).2, h0, hE 1 (by decide)]; rfl)
    (by rw [(S2 2 (by decide) (by decide)).1, (S2 2 (by decide) (by decide)).2, h0, hE 2 (by decide)]; rfl)
    (by rw [(o2 3 (by decide)).1, (o2 3 (by decide)).2, e1h]) e2h
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g.s0, (S2 0 (by decide) (by decide)).1, hB]
  · rw [g.s1, (S2 1 (by decide) (by decide)).1, hE 1 (by decide)]; rfl
  · rw [g.s2, (S2 2 (by decide) (by decide)).1, hE 2 (by decide)]; rfl
  · rw [g.s3, (o2 3 (by decide)).1, e1, hE 3 (by decide)]; rfl
  · rw [g.s4, e2, (o1 4 (by decide)).1, hE 4 (by decide)]; rfl
  · rw [g.c, c2, c1]

end NearCubicWires.WireExponent3_5.UnionMachine.CWParGen
