import Proof.Wire_3_5.UnionMachine.CWWords

/-! # C6 front, U5, the code writers: the retained bottoms of a `THR∘THR` circuit

The charged gates of a `THR∘THR` circuit are "the bottoms at retained top positions" (`Stars.thrGates`: the bottoms `i`
with `i ∈ C.top.support`), so the `THR∘THR` carrier writer appends to its bottom accumulator only the bottoms that the
top's support bitmap selects. The bitmap is the balanced list `encodeBoolList` of the support's members, so base's
traversal writes its atoms as the framed words `binary W b`, whose first bit is `b` (`binary` is little-endian).

* **`selOf`**: the retained words of a list of (bottom word, selector word) pairs, a pair being retained when its
  selector's first bit is `true`;
* **`selBody_spec`**: one pair; **`selLoop_spec`**: every pair;
* **`selW`** (streams `0` the bottoms' words, `1` the selectors, `2` the bottom accumulator, `3` the count
  accumulator): **`selW_spec`**, and its Step **`selStage`** (heads rewound).

Paper quantity of the main type: the charged gates of a `THR∘THR` circuit (P3:3401-3410), as bottom words. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWSel
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW skipFrameW skipFrame_spec)
open NearCubicWires.WireExponent3_5.PrimT.CarWM (copyFrameW copyFrame_spec rd_at rd_at1)

/-- A selector's bit: its first bit. -/
def selBit (s : List Bool) : Bool := s.getD 0 false

/-- **The retained words**: the first components of the pairs whose selector starts with `true`. -/
def selOf (ps : List (List Bool × List Bool)) : List (List Bool) :=
  (ps.filter fun p => selBit p.2).map Prod.fst

theorem selOf_nil : selOf [] = [] := rfl

theorem selOf_cons (p : List Bool × List Bool) (ps : List (List Bool × List Bool)) :
    selOf (p :: ps) = (if selBit p.2 then [p.1] else []) ++ selOf ps := by
  unfold selOf
  by_cases h : selBit p.2 = true
  · simp [List.filter_cons, h]
  · simp [List.filter_cons, h]

/-- The fuel of the selection loop. -/
def selCost (ps : List (List Bool × List Bool)) : ℕ :=
  (ps.map fun p => 16 * p.1.length + 6 * p.2.length + 33).sum + 1

section Loop
variable {ns nr : ℕ} (cap : ℕ)

/-- One pair: on a selector starting with `true`, copy the bottom word and count it; else skip it. -/
def selBody (A S B N : Fin (ns + 1)) : WM ns nr :=
  .seq (.fwd S) (.seq (.ifs S (.seq (copyFrameW A B) (.seq (.fwd A) (emitW N true))) (skipFrameW A))
    (.seq (.bwd S) (skipFrameW S)))

theorem frame_len (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  rw [NearCubicWires.WireExponent3_5.FinalPass.Tm.frame_eq_frameP]; simp

theorem frame_getD_one (s : List Bool) (hs : s ≠ []) (rest : List Bool) :
    (frame s ++ rest).getD 1 false = selBit s := by
  cases s with
  | nil => exact absurd rfl hs
  | cons b s => simp [selBit, frame]

/-- The selected branch: copy the bottom word, move past its end mark, count it. -/
theorem selT_spec (A B N : Fin (ns + 1)) (hAB : A ≠ B) (hAN : A ≠ N) (hBN : B ≠ N) (a preA restA : List Bool)
    (σ : WState ns nr) (hA : σ.st A = preA ++ (frame a ++ restA)) (hAh : σ.sh A = preA.length)
    (hB : σ.sh B = (σ.st B).length) (hN : σ.sh N = (σ.st N).length) :
    ∃ τ, WExec cap (.seq (copyFrameW A B) (.seq (.fwd A) (emitW N true))) σ τ (14 * a.length + 11) ∧
      τ.st B = σ.st B ++ frame a ∧ τ.sh B = (τ.st B).length ∧ τ.st N = σ.st N ++ [true] ∧
      τ.sh N = (τ.st N).length ∧ τ.st A = σ.st A ∧ τ.sh A = preA.length + (frame a).length ∧
      (∀ j, j ≠ A → j ≠ B → j ≠ N → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨σ1, s1, e1, e1h, a1, a1h, o1, v1, c1⟩ := copyFrame_spec cap A B hAB preA a restA σ hA hAh hB
  obtain ⟨σ2, s2, a2, a2h, o2, v2, c2⟩ := fwd_facts cap A σ1
  have N1 := o1 N (Ne.symm hAN) (Ne.symm hBN)
  have N2 := o2 N (Ne.symm hAN)
  obtain ⟨τ, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap N true σ2 (by rw [N2.1, N2.2, N1.1, N1.2, hN])
  have B2 := o2 B (Ne.symm hAB)
  have B3 := o3 B hBN
  have A3 := o3 A hAN
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega), ?_, ?_, ?_, e3h, ?_, ?_, ?_, ?_, ?_⟩
  · rw [B3.1, B2.1, e1]
  · rw [B3.2, B2.2, e1h, B3.1, B2.1]
  · rw [e3, N2.1, N1.1]
  · rw [A3.1, a2, a1]
  · rw [A3.2, a2h, a1h, frame_len]; omega
  · intro j h1 h2 h3
    exact ((o1 j h1 h2).trans' (o2 j h1)).trans' (o3 j h3)
  · rw [v3, v2, v1]
  · rw [c3, c2, c1]

/-- **One pair of the selection.** -/
theorem selBody_spec (A S B N : Fin (ns + 1)) (hAS : A ≠ S) (hAB : A ≠ B) (hAN : A ≠ N) (hSB : S ≠ B) (hSN : S ≠ N)
    (hBN : B ≠ N) (a s : List Bool) (hs : s ≠ []) (preA restA preS restS : List Bool) (σ : WState ns nr)
    (hA : σ.st A = preA ++ (frame a ++ restA)) (hAh : σ.sh A = preA.length)
    (hS : σ.st S = preS ++ (frame s ++ restS)) (hSh : σ.sh S = preS.length)
    (hB : σ.sh B = (σ.st B).length) (hN : σ.sh N = (σ.st N).length) :
    ∃ τ, WExec cap (selBody A S B N) σ τ (14 * a.length + 5 * s.length + 20) ∧
      τ.st B = σ.st B ++ (if selBit s then frame a else []) ∧ τ.sh B = (τ.st B).length ∧
      τ.st N = σ.st N ++ (if selBit s then [true] else []) ∧ τ.sh N = (τ.st N).length ∧
      τ.st A = σ.st A ∧ τ.sh A = preA.length + (frame a).length ∧
      τ.st S = σ.st S ∧ τ.sh S = preS.length + (frame s).length ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap S σ
  have A1 := o1 A hAS
  have B1 := o1 B (Ne.symm hSB)
  have N1 := o1 N (Ne.symm hSN)
  have hbit : wbit σ1 S = selBit s := by
    unfold wbit; rw [a1, a1h, hS, hSh, rd_at1, frame_getD_one s hs]
  -- the branch
  have hbr : ∃ σ2, WExec cap (.ifs S (.seq (copyFrameW A B) (.seq (.fwd A) (emitW N true))) (skipFrameW A)) σ1 σ2
      (14 * a.length + 12) ∧
      σ2.st B = σ.st B ++ (if selBit s then frame a else []) ∧ σ2.sh B = (σ2.st B).length ∧
      σ2.st N = σ.st N ++ (if selBit s then [true] else []) ∧ σ2.sh N = (σ2.st N).length ∧
      σ2.st A = σ.st A ∧ σ2.sh A = preA.length + (frame a).length ∧ Same σ1 σ2 S ∧ σ2.val = σ.val ∧
      σ2.cell = σ.cell := by
    cases hb : selBit s
    · have sk := skipFrame_spec cap A preA restA a σ1 (by rw [A1.1, hA]) (by rw [A1.2, hAh])
      refine ⟨_, WExec.mono (WExec.ifsF (by rw [hbit, hb]) sk) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [B1.1]
      · simp [Function.update_of_ne (Ne.symm hAB), B1.1, B1.2, hB]
      · simp [N1.1]
      · simp [Function.update_of_ne (Ne.symm hAN), N1.1, N1.2, hN]
      · simp [A1.1]
      · simp
      · exact ⟨rfl, by simp [Function.update_of_ne (Ne.symm hAS)]⟩
      · simp [v1]
      · simp [c1]
    · obtain ⟨σ2, t2, e2, e2h, n2, n2h, a2, a2h, o2, v2, c2⟩ := selT_spec cap A B N hAB hAN hBN a preA restA σ1
        (by rw [A1.1, hA]) (by rw [A1.2, hAh]) (by rw [B1.1, B1.2, hB]) (by rw [N1.1, N1.2, hN])
      refine ⟨σ2, WExec.mono (WExec.ifsT (by rw [hbit, hb]) t2) (by omega), ?_, e2h, ?_, n2h, ?_, a2h,
        o2 S (Ne.symm hAS) hSB hSN, by rw [v2, v1], by rw [c2, c1]⟩
      · rw [e2, B1.1]; simp
      · rw [n2, N1.1]; simp
      · rw [a2, A1.1]
  obtain ⟨σ2, s2, e2, e2h, n2, n2h, a2, a2h, S2, v2, c2⟩ := hbr
  -- back to the selector's start, then past it
  have s3 := WExec.bwd (cap := cap) S σ2
  set σ3 := σ2.seth S (σ2.sh S - 1) with hσ3
  have s4 := skipFrame_spec cap S preS restS s σ3 (by simp [hσ3, S2.1, a1, hS])
    (by simp [hσ3, S2.2, a1h, hSh])
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [hσ3, e2]
  · simp [hσ3, Function.update_of_ne (Ne.symm hSB), e2h, e2]
  · simp [hσ3, n2]
  · simp [hσ3, Function.update_of_ne (Ne.symm hSN), n2h, n2]
  · simp [hσ3, a2]
  · simp [hσ3, Function.update_of_ne hAS, a2h]
  · simp [hσ3, S2.1, a1]
  · simp
  · simp [hσ3, v2]
  · simp [hσ3, c2]

/-- **The selection loop**: every pair, the retained bottom words appended to `B`, their count to `N`. -/
theorem selLoop_spec (A S B N : Fin (ns + 1)) (hAS : A ≠ S) (hAB : A ≠ B) (hAN : A ≠ N) (hSB : S ≠ B)
    (hSN : S ≠ N) (hBN : B ≠ N) :
    ∀ (ps : List (List Bool × List Bool)) (preA tailA preS : List Bool) (σ : WState ns nr),
      (∀ p ∈ ps, p.2 ≠ []) →
      σ.st A = preA ++ ((ps.map Prod.fst).flatMap frame ++ tailA) → σ.sh A = preA.length →
      σ.st S = preS ++ (ps.map Prod.snd).flatMap frame → σ.sh S = preS.length →
      σ.sh B = (σ.st B).length → σ.sh N = (σ.st N).length →
      ∃ τ, WExec cap (.whs S (selBody A S B N)) σ τ (selCost ps) ∧
        τ.st B = σ.st B ++ (selOf ps).flatMap frame ∧ τ.sh B = (τ.st B).length ∧
        τ.st N = σ.st N ++ List.replicate (selOf ps).length true ∧ τ.sh N = (τ.st N).length ∧
        τ.st A = σ.st A ∧ τ.st S = σ.st S ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], preA, tailA, preS, σ, _, _, _, hS, hSh, hB, hN => by
    have hz : wbit σ S = false := by
      unfold wbit; rw [hS, hSh]; unfold readTapeBit; simp
    refine ⟨σ, WExec.mono (WExec.whsF hz) (by simp [selCost]), ?_, hB, ?_, hN, rfl, rfl, rfl, rfl⟩
    · simp [selOf_nil]
    · simp [selOf_nil]
  | p :: ps, preA, tailA, preS, σ, hne, hA, hAh, hS, hSh, hB, hN => by
    have hs : p.2 ≠ [] := hne p (by simp)
    have hA' : σ.st A = preA ++ (frame p.1 ++ ((ps.map Prod.fst).flatMap frame ++ tailA)) := by
      rw [hA]; simp [List.append_assoc]
    have hS' : σ.st S = preS ++ (frame p.2 ++ (ps.map Prod.snd).flatMap frame) := by
      rw [hS]; simp
    obtain ⟨σ1, s1, e1, e1h, n1, n1h, a1, a1h, t1, t1h, v1, c1⟩ := selBody_spec cap A S B N hAS hAB hAN hSB hSN hBN
      p.1 p.2 hs preA _ preS _ σ hA' hAh hS' hSh hB hN
    obtain ⟨τ, s2, e2, e2h, n2, n2h, a2, t2, v2, c2⟩ := selLoop_spec A S B N hAS hAB hAN hSB hSN hBN ps
      (preA ++ frame p.1) tailA (preS ++ frame p.2) σ1 (fun q hq => hne q (by simp [hq]))
      (by rw [a1, hA']; simp) (by rw [a1h]; simp) (by rw [t1, hS']; simp) (by rw [t1h]; simp) e1h n1h
    have hr : wbit σ S = true := by
      unfold wbit; rw [hS', hSh]
      exact CWWords.rd_frame_head preS p.2 _ hs
    have hc : selCost (p :: ps) = (16 * p.1.length + 6 * p.2.length + 33) + selCost ps := by
      simp [selCost, List.map_cons, List.sum_cons]; omega
    refine ⟨τ, WExec.mono (WExec.whsT hr s1 s2) (by rw [hc]; omega), ?_, e2h, ?_, n2h, ?_, ?_, ?_, ?_⟩
    · rw [e2, e1, selOf_cons]
      by_cases hb : selBit p.2 = true
      · simp [hb, List.append_assoc]
      · simp [hb]
    · rw [n2, n1, selOf_cons]
      by_cases hb : selBit p.2 = true
      · simp [hb, List.replicate_succ]
      · simp [hb]
    · rw [a2, a1]
    · rw [t2, t1]
    · rw [v2, v1]
    · rw [c2, c1]

end Loop

/-! ## The program -/

/-- **The selection** (streams `0` the bottoms' words, `1` the selectors, `2` the bottom accumulator, `3` the count
accumulator `false :: 1^n`): move to the accumulators' ends, then the selection loop. -/
def selW : WM 3 0 :=
  .seq (.whs 2 (skipFrameW 2)) (.seq (.fwd 3) (.seq (.whs 3 (.fwd 3)) (.whs 1 (selBody 0 1 2 3))))

/-- The selection's fuel. -/
def selWCost (ps : List (List Bool × List Bool)) (bs : List (List Bool)) (n : ℕ) : ℕ :=
  6 * (bs.flatMap frame).length + 3 * n + selCost ps + 10

theorem selW_spec (cap : ℕ) (ps : List (List Bool × List Bool)) (hps : ∀ p ∈ ps, p.2 ≠ [])
    (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b ≠ []) (n : ℕ) (σ : WState 3 0) (h0 : ∀ j, σ.sh j = 0)
    (hA : σ.st 0 = (ps.map Prod.fst).flatMap frame) (hS : σ.st 1 = (ps.map Prod.snd).flatMap frame)
    (hB : σ.st 2 = bs.flatMap frame) (hN : σ.st 3 = false :: List.replicate n true) :
    ∃ τ, WExec cap selW σ τ (selWCost ps bs n) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = σ.st 1 ∧
      τ.st 2 = (bs ++ selOf ps).flatMap frame ∧ τ.st 3 = false :: List.replicate (n + (selOf ps).length) true ∧
      τ.cell = σ.cell := by
  have s1 := CWWords.skipWords_spec cap (2 : Fin 4) bs [] σ hbs (by rw [hB]; rfl) (by rw [h0]; rfl)
  set σ1 := σ.seth 2 ([].length + (bs.flatMap frame).length) with hσ1
  obtain ⟨σ2, s2, a2, a2h, o2, v2, c2⟩ := fwd_facts cap (3 : Fin 4) σ1
  have s3 := CWWords.onesSkip_spec cap (3 : Fin 4) [false] n σ2 (by rw [a2]; simp [hσ1, hN])
    (by rw [a2h]; simp [hσ1, h0])
  set σ3 := σ2.seth 3 ([false].length + n) with hσ3
  have A3 : σ3.st 0 = σ.st 0 ∧ σ3.sh 0 = 0 := by
    have := o2 0 (by decide); simp [hσ3, this.1, this.2, hσ1, h0]
  have S3 : σ3.st 1 = σ.st 1 ∧ σ3.sh 1 = 0 := by
    have := o2 1 (by decide); simp [hσ3, this.1, this.2, hσ1, h0]
  have B3 : σ3.st 2 = σ.st 2 ∧ σ3.sh 2 = (σ3.st 2).length := by
    have := o2 2 (by decide); simp [hσ3, this.1, this.2, hσ1, hB]
  have N3 : σ3.st 3 = σ.st 3 ∧ σ3.sh 3 = (σ3.st 3).length := by
    simp [hσ3, a2, hσ1, hN]; omega
  obtain ⟨τ, s4, e4, e4h, n4, n4h, t0, t1, v4, c4⟩ := selLoop_spec cap (0 : Fin 4) 1 2 3 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ps [] [] [] σ3 hps (by rw [A3.1, hA]; simp) (by rw [A3.2]; rfl)
    (by rw [S3.1, hS]; rfl) (by rw [S3.2]; rfl) B3.2 N3.2
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by unfold selWCost; simp; omega),
    by rw [t0, A3.1], by rw [t1, S3.1], ?_, ?_, ?_⟩
  · rw [e4, B3.1, hB, List.flatMap_append]
  · rw [n4, N3.1, hN, List.replicate_add]; simp
  · rw [c4]; simp [hσ3, c2, hσ1]

/-! ## The Step -/

def σSel (A S B N : List Bool) : WState 3 0 := ⟨fun _ => 0, ![A, S, B, N], fun r => r.elim0, false⟩

/-- The selection's entry bank: the bottoms' words, the cell, the selectors, the two accumulators, the log. -/
def selIn (A S B N : List Bool) : Fin 6 → List Bool :=
  Fin.addCases (m := 3 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σSel A S B N)).A (fun _ => [])

theorem selIn_val (A S B N : List Bool) (j : Fin 6) :
    selIn A S B N j = if j.val = 0 then A else if j.val = 1 then [false] else if j.val = 2 then S else
      if j.val = 3 then B else if j.val = 4 then N else [] := by
  fin_cases j <;> rfl

/-- **The selection as a Step.** -/
theorem selStage (ps : List (List Bool × List Bool)) (hps : ∀ p ∈ ps, p.2 ≠ []) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, b ≠ []) (n : ℕ) :
    ∃ o : Fin 6 → List Bool,
    Step (Rewind.machine selW.toProg.compile) (2 * selWCost ps bs n + 2) (fun _ => 0)
      (selIn ((ps.map Prod.fst).flatMap frame) ((ps.map Prod.snd).flatMap frame) (bs.flatMap frame)
        (false :: List.replicate n true)) (fun _ => 0) o ∧
    o 0 = (ps.map Prod.fst).flatMap frame ∧ o 1 = [false] ∧ o 2 = (ps.map Prod.snd).flatMap frame ∧
    o 3 = (bs ++ selOf ps).flatMap frame ∧ o 4 = false :: List.replicate (n + (selOf ps).length) true := by
  set σ := σSel ((ps.map Prod.fst).flatMap frame) ((ps.map Prod.snd).flatMap frame) (bs.flatMap frame)
    (false :: List.replicate n true) with hσ
  obtain ⟨τ, hw, e0, e1, e2, e3, ec⟩ := selW_spec 0 ps hps bs hbs n σ (fun _ => rfl) rfl rfl rfl rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 selW σ τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 6) = Fin.castAdd 1 (0 : Fin 5) from rfl, ho]; exact e0
  · rw [show (1 : Fin 6) = Fin.castAdd 1 (1 : Fin 5) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 6) = Fin.castAdd 1 (2 : Fin 5) from rfl, ho]; exact e1
  · rw [show (3 : Fin 6) = Fin.castAdd 1 (3 : Fin 5) from rfl, ho]; exact e2
  · rw [show (4 : Fin 6) = Fin.castAdd 1 (4 : Fin 5) from rfl, ho]; exact e3

end NearCubicWires.WireExponent3_5.UnionMachine.CWSel
