import Proof.Wire_3_5.UnionMachine.CWParGen

/-! # C6 front, U5, the code writers: the parity's top fields

The two parity atoms differ only in their top (`unionParityAtom`):
* `SYM∘THR`: the top table `c ↦ [c odd]` over `c ≤ k`, coded `encodeBoolList` — fields `sgl (oddL (k+1))` with count
  word `false :: 1^(k+1)` (**`topS_spec`**);
* `THR∘THR`: base's `thresholdParityTopGate k` — weights `+1, -1, +1, …` (`encodeInt 1 = 9`, `encodeInt (-1) = 10`),
  threshold `1`, support everything — fields `altF k` and `sgl (true^k)` (**`topT_spec`**).
Both are written from the count word `false :: 1^k`, a toggle cell tracking the parity of the index.

Paper quantity of the main types: the atoms of the parity atoms' top codes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParTop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt (sgl sgl_cons sgl_append)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParGen (emitL emitL_spec w9)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-- The `SYM∘THR` parity's top table, `c ↦ [c odd]` for `c < n`. -/
def oddL (n : ℕ) : List Bool := (List.range n).map fun c => decide (Odd c)

theorem oddL_succ (n : ℕ) : oddL (n + 1) = oddL n ++ [decide (Odd n)] := by
  unfold oddL; rw [List.range_succ, List.map_append]; rfl

/-- The code of the weight `-1` (`encodeInt (-1) = 10`), least significant bit first. -/
def w10 : List Bool := [false, true, false, true]

/-- The `THR∘THR` parity top's weights' fields: `9, 10, 9, …` (`k` of them). -/
def altF (n : ℕ) : List Bool := ((List.range n).map fun i => if Even i then w9 else w10).flatMap frame

theorem altF_succ (n : ℕ) : altF (n + 1) = altF n ++ frame (if Even n then w9 else w10) := by
  unfold altF; rw [List.range_succ, List.map_append, List.flatMap_append]; simp

theorem sgl_rep_succ (n : ℕ) : sgl (List.replicate (n + 1) true) = sgl (List.replicate n true) ++ [true, true, false] := by
  rw [List.replicate_succ', sgl_append]; rfl

theorem word_succ (n : ℕ) : CompareMachine.word (n + 1) = CompareMachine.word n ++ [true] := by
  unfold CompareMachine.word; rw [List.replicate_succ']; rfl

/-! ## The `SYM∘THR` top -/

/-- One index: flip the toggle, then its field `[odd]` and one count. -/
def sBody : WM 3 0 :=
  .seq (.fwd 0) (.seq (.ifs 3 (.wr 3 false) (.wr 3 true)) (.seq (emitW 1 true)
    (.seq (.ifs 3 (emitW 1 true) (emitW 1 false)) (.seq (emitW 1 false) (emitW 2 true)))))

/-- **The `SYM∘THR` top fields** (streams `0` the count word `false :: 1^k`, `1` the fields, `2` their count word,
`3` the toggle). -/
def topS : WM 3 0 :=
  .seq (emitL 1 [true, false, false]) (.seq (emitL 2 [false, true]) (.seq (.wr 3 false) (.seq (.fwd 0) (.whs 0 sBody))))

theorem sLoop_spec (cap : ℕ) : ∀ (d c : ℕ) (σ : WState 3 0), σ.st 0 = CompareMachine.word (c + d) →
    σ.sh 0 = c + 1 → σ.st 1 = sgl (oddL (c + 1)) → σ.sh 1 = (σ.st 1).length →
    σ.st 2 = CompareMachine.word (c + 1) → σ.sh 2 = (σ.st 2).length → σ.st 3 = [decide (Odd c)] → σ.sh 3 = 0 →
    ∃ τ, WExec cap (.whs 0 sBody) σ τ (d * 24 + 1) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = sgl (oddL (c + d + 1)) ∧
      τ.st 2 = CompareMachine.word (c + d + 1) ∧ τ.cell = σ.cell
  | 0, c, σ, h0, h0h, h1, _, h2, _, _, _ => by
    have hz : wbit σ 0 = false := by
      unfold wbit; rw [h0, h0h]; unfold readTapeBit CompareMachine.word; simp
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, by rw [h1], by rw [h2], rfl⟩
  | d + 1, c, σ, h0, h0h, h1, h1h, h2, h2h, h3, h3h => by
    have hr : wbit σ 0 = true := by
      unfold wbit; rw [h0, h0h]; unfold readTapeBit CompareMachine.word
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap (0 : Fin 4) σ
    have T1 := o1 3 (by decide)
    have hb1 : wbit σ1 3 = decide (Odd c) := by unfold wbit; rw [T1.1, T1.2, h3, h3h]; rfl
    -- flip the toggle
    have s2 : WExec cap (.ifs 3 (.wr 3 false) (.wr 3 true)) σ1 (σ1.sets 3 [decide (Odd (c + 1))]) 2 := by
      have hw : ∀ v : Bool, σ1.sets 3 (writeTapeBit (σ1.st 3) (σ1.sh 3) v) = σ1.sets 3 [v] := by
        intro v; rw [T1.1, T1.2, h3, h3h]; rfl
      rcases Nat.even_or_odd c with he | ho
      · have hc : decide (Odd c) = false := by simp [Nat.not_odd_iff_even.mpr he]
        have hc1 : decide (Odd (c + 1)) = true := by simp [Even.add_one he]
        rw [hc1, ← hw]; exact WExec.ifsF (by rw [hb1, hc]) (WExec.wr 3 true σ1)
      · have hc : decide (Odd c) = true := by simp [ho]
        have hc1 : decide (Odd (c + 1)) = false := by simp [Nat.not_odd_iff_even.mpr (Odd.add_one ho)]
        rw [hc1, ← hw]; exact WExec.ifsT (by rw [hb1, hc]) (WExec.wr 3 false σ1)
    set σ2 := σ1.sets 3 [decide (Odd (c + 1))] with hσ2
    have S2 : ∀ j : Fin 4, j ≠ 3 → σ2.st j = σ1.st j ∧ σ2.sh j = σ1.sh j := fun j hj =>
      ⟨by simp [hσ2, Function.update_of_ne hj], rfl⟩
    obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap (1 : Fin 4) true σ2
      (by rw [(S2 1 (by decide)).1, (S2 1 (by decide)).2, (o1 1 (by decide)).1, (o1 1 (by decide)).2, h1h])
    have hb3 : wbit σ3 3 = decide (Odd (c + 1)) := by
      unfold wbit; rw [(o3 3 (by decide)).1, (o3 3 (by decide)).2]
      simp [hσ2, T1.2, h3h, readTapeBit]
    obtain ⟨σ4, s4', e4, e4h, o4, v4, c4⟩ := emit_facts cap (1 : Fin 4) (decide (Odd (c + 1))) σ3 e3h
    have s4 : WExec cap (.ifs 3 (emitW 1 true) (emitW 1 false)) σ3 σ4 4 := by
      cases hv : decide (Odd (c + 1))
      · rw [hv] at s4' hb3; exact WExec.ifsF hb3 s4'
      · rw [hv] at s4' hb3; exact WExec.ifsT hb3 s4'
    obtain ⟨σ5, s5, e5, e5h, o5, v5, c5⟩ := emit_facts cap (1 : Fin 4) false σ4 e4h
    have N5 := ((o3 2 (by decide)).trans' (o4 2 (by decide))).trans' (o5 2 (by decide))
    obtain ⟨σ6, s6, e6, e6h, o6, v6, c6⟩ := emit_facts cap (2 : Fin 4) true σ5
      (by rw [N5.1, N5.2, (S2 2 (by decide)).1, (S2 2 (by decide)).2, (o1 2 (by decide)).1, (o1 2 (by decide)).2, h2h])
    have Z6 := (((o3 0 (by decide)).trans' (o4 0 (by decide))).trans' (o5 0 (by decide))).trans' (o6 0 (by decide))
    have T6 := (((o3 3 (by decide)).trans' (o4 3 (by decide))).trans' (o5 3 (by decide))).trans' (o6 3 (by decide))
    obtain ⟨τ, s7, e7, e71, e72, c7⟩ := sLoop_spec cap d (c + 1) σ6
      (by rw [Z6.1, (S2 0 (by decide)).1, a1, h0]; congr 1; omega)
      (by rw [Z6.2, (S2 0 (by decide)).2, a1h, h0h])
      (by rw [(o6 1 (by decide)).1, e5, e4, e3, (S2 1 (by decide)).1, (o1 1 (by decide)).1, h1, oddL_succ (c + 1),
          sgl_append]; simp [sgl])
      (by rw [(o6 1 (by decide)).2, e5h, (o6 1 (by decide)).1])
      (by rw [e6, N5.1, (S2 2 (by decide)).1, (o1 2 (by decide)).1, h2]; exact (word_succ (c + 1)).symm)
      e6h (by rw [T6.1]; simp [hσ2]) (by rw [T6.2]; simp [hσ2, T1.2, h3h])
    have body : WExec cap sBody σ σ6 (1 + 1 + (2 + 1 + (3 + 1 + (4 + 1 + (3 + 1 + 3))))) :=
      WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))
    refine ⟨τ, WExec.mono (WExec.whsT hr body s7) (by ring_nf; omega), ?_, ?_, ?_, ?_⟩
    · rw [e7, Z6.1, (S2 0 (by decide)).1, a1]
    · rw [e71]; congr 2; omega
    · rw [e72]; congr 1; omega
    · rw [c7, c6, c5, c4, c3]; simp [hσ2, c1]

theorem topS_spec (cap k : ℕ) (σ : WState 3 0) (h0 : ∀ j, σ.sh j = 0) (hK : σ.st 0 = CompareMachine.word k)
    (h1 : σ.st 1 = []) (h2 : σ.st 2 = []) (h3 : σ.st 3 = []) :
    ∃ τ, WExec cap topS σ τ (k * 24 + 30) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = sgl (oddL (k + 1)) ∧
      τ.st 2 = CompareMachine.word (k + 1) ∧ τ.cell = σ.cell := by
  obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emitL_spec cap (1 : Fin 4) [true, false, false] σ (by rw [h0, h1]; rfl)
  obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_spec cap (2 : Fin 4) [false, true] σ1
    (by rw [(o1 2 (by decide)).1, (o1 2 (by decide)).2, h0, h2]; rfl)
  have s3 := WExec.wr (cap := cap) (3 : Fin 4) false σ2
  set σ3 := σ2.sets 3 (writeTapeBit (σ2.st 3) (σ2.sh 3) false) with hσ3
  have hT3 : σ3.st 3 = [false] := by
    simp only [hσ3, WState.sets_st, Function.update_self]
    rw [(o2 3 (by decide)).1, (o2 3 (by decide)).2, (o1 3 (by decide)).1, (o1 3 (by decide)).2, h3, h0]; rfl
  obtain ⟨σ4, s4, a4, a4h, o4, v4, c4⟩ := fwd_facts cap (0 : Fin 4) σ3
  obtain ⟨τ, s5, e5, e51, e52, c5⟩ := sLoop_spec cap k 0 σ4
    (by rw [a4]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne (by decide), (o2 0 (by decide)).1,
      (o1 0 (by decide)).1, hK]; simp)
    (by rw [a4h]; simp only [hσ3, WState.sets_sh]; rw [(o2 0 (by decide)).2, (o1 0 (by decide)).2, h0])
    (by rw [(o4 1 (by decide)).1]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne (by decide),
      (o2 1 (by decide)).1, e1, h1]; rfl)
    (by rw [(o4 1 (by decide)).1, (o4 1 (by decide)).2]; simp only [hσ3, WState.sets_st, WState.sets_sh]
        rw [Function.update_of_ne (by decide), (o2 1 (by decide)).1, (o2 1 (by decide)).2, e1h])
    (by rw [(o4 2 (by decide)).1]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne (by decide), e2,
      (o1 2 (by decide)).1, h2]; rfl)
    (by rw [(o4 2 (by decide)).1, (o4 2 (by decide)).2]; simp only [hσ3, WState.sets_st, WState.sets_sh]
        rw [Function.update_of_ne (by decide), e2h])
    (by rw [(o4 3 (by decide)).1, hT3]; rfl)
    (by rw [(o4 3 (by decide)).2]; simp only [hσ3, WState.sets_sh]; rw [(o2 3 (by decide)).2, (o1 3 (by decide)).2, h0])
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) (by simp; omega),
    ?_, by rw [e51]; simp, by rw [e52]; simp, ?_⟩
  · rw [e5, a4]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne (by decide), (o2 0 (by decide)).1,
      (o1 0 (by decide)).1]
  · rw [c5, c4]; simp only [hσ3, WState.sets_cell]; rw [c2, c1]

/-! ## The `THR∘THR` top -/

/-- One index: its weight's field (`9` at an even index, `10` at an odd one), the toggle flipped, one support field. -/
def tBody : WM 3 0 :=
  .seq (.fwd 0) (.seq (.ifs 3 (emitL 1 (frame w9)) (emitL 1 (frame w10)))
    (.seq (.ifs 3 (.wr 3 false) (.wr 3 true)) (emitL 2 [true, true, false])))

/-- **The `THR∘THR` top fields** (streams `0` the count word `false :: 1^k`, `1` the weights' fields, `2` the support's
fields, `3` the toggle). -/
def topT : WM 3 0 := .seq (.wr 3 true) (.seq (.fwd 0) (.whs 0 tBody))

theorem tLoop_spec (cap : ℕ) : ∀ (d i : ℕ) (σ : WState 3 0), σ.st 0 = CompareMachine.word (i + d) →
    σ.sh 0 = i + 1 → σ.st 1 = altF i → σ.sh 1 = (σ.st 1).length →
    σ.st 2 = sgl (List.replicate i true) → σ.sh 2 = (σ.st 2).length → σ.st 3 = [decide (Even i)] → σ.sh 3 = 0 →
    ∃ τ, WExec cap (.whs 0 tBody) σ τ (d * 60 + 1) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = altF (i + d) ∧
      τ.st 2 = sgl (List.replicate (i + d) true) ∧ τ.cell = σ.cell
  | 0, i, σ, h0, h0h, h1, _, h2, _, _, _ => by
    have hz : wbit σ 0 = false := by
      unfold wbit; rw [h0, h0h]; unfold readTapeBit CompareMachine.word; simp
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, by rw [h1]; rfl, by rw [h2]; rfl, rfl⟩
  | d + 1, i, σ, h0, h0h, h1, h1h, h2, h2h, h3, h3h => by
    have hr : wbit σ 0 = true := by
      unfold wbit; rw [h0, h0h]; unfold readTapeBit CompareMachine.word
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap (0 : Fin 4) σ
    have T1 := o1 3 (by decide)
    have hb1 : wbit σ1 3 = decide (Even i) := by unfold wbit; rw [T1.1, T1.2, h3, h3h]; rfl
    -- the weight's field
    have hbr : ∃ σ2, WExec cap (.ifs 3 (emitL 1 (frame w9)) (emitL 1 (frame w10))) σ1 σ2 37 ∧
        σ2.st 1 = altF (i + 1) ∧ σ2.sh 1 = (σ2.st 1).length ∧ (∀ j, j ≠ 1 → Same σ1 σ2 j) ∧ σ2.cell = σ1.cell := by
      have hl1 : σ1.sh 1 = (σ1.st 1).length := by
        rw [(o1 1 (by decide)).1, (o1 1 (by decide)).2, h1h]
      by_cases he : Even i
      · obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_spec cap (1 : Fin 4) (frame w9) σ1 hl1
        refine ⟨σ2, WExec.mono (WExec.ifsT (by rw [hb1]; simp [he]) s2) (by simp [frame, w9]), ?_, e2h, o2, c2⟩
        rw [e2, (o1 1 (by decide)).1, h1, altF_succ]; simp [he]
      · obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_spec cap (1 : Fin 4) (frame w10) σ1 hl1
        refine ⟨σ2, WExec.mono (WExec.ifsF (by rw [hb1]; simp [he]) s2) (by simp [frame, w10]), ?_, e2h, o2, c2⟩
        rw [e2, (o1 1 (by decide)).1, h1, altF_succ]; simp [he]
    obtain ⟨σ2, s2, e2, e2h, o2, c2⟩ := hbr
    have T2 := T1.trans' (o2 3 (by decide))
    have hb2 : wbit σ2 3 = decide (Even i) := by unfold wbit; rw [T2.1, T2.2, h3, h3h]; rfl
    -- flip the toggle
    have s3 : WExec cap (.ifs 3 (.wr 3 false) (.wr 3 true)) σ2 (σ2.sets 3 [decide (Even (i + 1))]) 2 := by
      have hw : ∀ v : Bool, σ2.sets 3 (writeTapeBit (σ2.st 3) (σ2.sh 3) v) = σ2.sets 3 [v] := by
        intro v; rw [T2.1, T2.2, h3, h3h]; rfl
      by_cases he : Even i
      · have hc1 : decide (Even (i + 1)) = false := by simp [Nat.even_add_one, he]
        rw [hc1, ← hw]; exact WExec.ifsT (by rw [hb2]; simp [he]) (WExec.wr 3 false σ2)
      · have hc1 : decide (Even (i + 1)) = true := by simp [Nat.even_add_one, he]
        rw [hc1, ← hw]; exact WExec.ifsF (by rw [hb2]; simp [he]) (WExec.wr 3 true σ2)
    set σ3 := σ2.sets 3 [decide (Even (i + 1))] with hσ3
    obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := emitL_spec cap (2 : Fin 4) [true, true, false] σ3
      (by simp only [hσ3, WState.sets_st, WState.sets_sh]
          rw [Function.update_of_ne (by decide), (o2 2 (by decide)).1, (o2 2 (by decide)).2, (o1 2 (by decide)).1,
            (o1 2 (by decide)).2, h2h])
    have Z4 : σ4.st 0 = σ.st 0 ∧ σ4.sh 0 = i + 2 := by
      rw [(o4 0 (by decide)).1, (o4 0 (by decide)).2]
      simp only [hσ3, WState.sets_st, WState.sets_sh]
      rw [Function.update_of_ne (by decide), (o2 0 (by decide)).1, (o2 0 (by decide)).2, a1, a1h, h0h]
      exact ⟨rfl, rfl⟩
    obtain ⟨τ, s5, e5, e51, e52, c5⟩ := tLoop_spec cap d (i + 1) σ4
      (by rw [Z4.1, h0]; congr 1; omega) (by rw [Z4.2])
      (by rw [(o4 1 (by decide)).1]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne (by decide), e2])
      (by rw [(o4 1 (by decide)).1, (o4 1 (by decide)).2]; simp only [hσ3, WState.sets_st, WState.sets_sh]
          rw [Function.update_of_ne (by decide), e2h])
      (by rw [e4]; simp only [hσ3, WState.sets_st]
          rw [Function.update_of_ne (by decide), (o2 2 (by decide)).1, (o1 2 (by decide)).1, h2, sgl_rep_succ])
      e4h (by rw [(o4 3 (by decide)).1]; simp [hσ3])
      (by rw [(o4 3 (by decide)).2]; simp only [hσ3, WState.sets_sh]; rw [T2.2, h3h])
    have body : WExec cap tBody σ σ4 (1 + 1 + (37 + 1 + (2 + 1 + 12))) :=
      WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.mono s4 (by simp))))
    refine ⟨τ, WExec.mono (WExec.whsT hr body s5) (by ring_nf; omega), ?_, ?_, ?_, ?_⟩
    · rw [e5, Z4.1]
    · rw [e51]; congr 1; omega
    · rw [e52]; congr 2; omega
    · rw [c5, c4]; simp [hσ3, c2, c1]

theorem topT_spec (cap k : ℕ) (σ : WState 3 0) (h0 : ∀ j, σ.sh j = 0) (hK : σ.st 0 = CompareMachine.word k)
    (h1 : σ.st 1 = []) (h2 : σ.st 2 = []) (h3 : σ.st 3 = []) :
    ∃ τ, WExec cap topT σ τ (k * 60 + 10) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = altF k ∧
      τ.st 2 = sgl (List.replicate k true) ∧ τ.cell = σ.cell := by
  have s1 := WExec.wr (cap := cap) (3 : Fin 4) true σ
  set σ1 := σ.sets 3 (writeTapeBit (σ.st 3) (σ.sh 3) true) with hσ1
  obtain ⟨σ2, s2, a2, a2h, o2, v2, c2⟩ := fwd_facts cap (0 : Fin 4) σ1
  obtain ⟨τ, s3, e3, e31, e32, c3⟩ := tLoop_spec cap k 0 σ2
    (by rw [a2]; simp only [hσ1, WState.sets_st]; rw [Function.update_of_ne (by decide), hK]; simp)
    (by rw [a2h]; simp [hσ1, h0])
    (by rw [(o2 1 (by decide)).1]; simp only [hσ1, WState.sets_st]; rw [Function.update_of_ne (by decide), h1]; rfl)
    (by rw [(o2 1 (by decide)).1, (o2 1 (by decide)).2]; simp [hσ1, h0, h1])
    (by rw [(o2 2 (by decide)).1]; simp only [hσ1, WState.sets_st]; rw [Function.update_of_ne (by decide), h2]; rfl)
    (by rw [(o2 2 (by decide)).1, (o2 2 (by decide)).2]; simp [hσ1, h0, h2])
    (by rw [(o2 3 (by decide)).1]; simp [hσ1, h3, h0, writeTapeBit])
    (by rw [(o2 3 (by decide)).2]; simp [hσ1, h0])
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega), ?_, by rw [e31]; simp, by rw [e32]; simp, ?_⟩
  · rw [e3, a2]; simp only [hσ1, WState.sets_st]; rw [Function.update_of_ne (by decide)]
  · rw [c3, c2]; simp [hσ1]

end NearCubicWires.WireExponent3_5.UnionMachine.CWParTop
