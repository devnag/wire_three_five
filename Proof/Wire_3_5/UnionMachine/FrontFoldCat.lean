import Proof.Wire_3_5.UnionMachine.CWWords

/-! # C6 front, U5, the writers' fold (b): the carrier input and the envelope bit

"The carrier of a variable: the charged gates of its atoms, and of its encoding parity if systematic" (P3:3409-3410,
3432-3433): the carrier writer reads the codes of the variable's atoms, then (for a systematic variable) its encoding
parity's code. Two register-free word programs of the fold's round:
* **`catW`**: from the atoms' codes `frame a`, the parity's code `frame p`, the round counter `1^{X+1}` and the
  systematic count `1^sys`: `frame (a ++ if X < sys then p else [])` (**`catStage`**);
* **`efW`**: from the envelope stage's `frame [b]` and the round counter: `b` appended to the flag string of length
  `X` (**`efStage`**).

Paper quantity of the main types: the carrier writer's input (the codes of the circuits whose gates form the carrier). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldCat
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW wm_step wenc_H_zero)
open NearCubicWires.WireExponent3_5.PrimT.CarWM (copyBodyW copyLoop_spec rd_at)

section Words
variable {ns nr : ℕ} (cap : ℕ)

/-- **Along the counter** `C` (a run of `n` ones, then a `false`), move `S` by `n`. -/
theorem skipAlong_spec (C S : Fin (ns + 1)) (hCS : C ≠ S) (rc : List Bool) (hrc : rc.getD 0 false = false) :
    ∀ (n : ℕ) (pre : List Bool) (σ : WState ns nr), σ.st C = pre ++ (List.replicate n true ++ rc) →
      σ.sh C = pre.length →
      ∃ τ, WExec cap (.whs C (.seq (.fwd S) (.fwd C))) σ τ (5 * n + 1) ∧ τ.st = σ.st ∧ τ.sh C = pre.length + n ∧
        τ.sh S = σ.sh S + n ∧ (∀ j, j ≠ C → j ≠ S → τ.sh j = σ.sh j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, pre, σ, hC, hCh => by
    have hz : wbit σ C = false := by
      simp only [wbit, hC, hCh, List.replicate_zero, List.nil_append, rd_at]; exact hrc
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, by simp [hCh], by simp, fun _ _ _ => rfl, rfl, rfl⟩
  | n + 1, pre, σ, hC, hCh => by
    have hw : wbit σ C = true := by
      simp only [wbit, hC, hCh, rd_at, List.replicate_succ, List.cons_append, List.getD_cons_zero]
    obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := fwd_facts cap S σ
    obtain ⟨σ2, s2, n2, n2h, o2, v2, c2⟩ := fwd_facts cap C σ1
    have C1 := o1 C hCS
    have S2 := o2 S (fun e => hCS e.symm)
    obtain ⟨τ, s3, e3, e3C, e3S, oth, v3, c3⟩ := skipAlong_spec C S hCS rc hrc n (pre ++ [true]) σ2
      (by rw [n2, C1.1, hC]; simp [List.replicate_succ]) (by rw [n2h, C1.2, hCh]; simp)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e3]; funext j
      by_cases hjC : j = C
      · subst hjC; rw [n2, C1.1]
      · by_cases hjS : j = S
        · subst hjS; rw [S2.1, n1]
        · rw [(o2 j hjC).1, (o1 j hjS).1]
    · rw [e3C]; simp; omega
    · rw [e3S, S2.2, n1h]; omega
    · intro j h1 h2; rw [oth j h1 h2, (o2 j h1).2, (o1 j h2).2]
    · rw [v3, v2, v1]
    · rw [c3, c2, c1]

theorem frameP_app (l l' : List Bool) : frameP (l ++ l') = frameP l ++ frameP l' := by
  simp [frameP, List.flatMap_append]

end Words

/-! ## The carrier input -/

/-- **The carrier input** (streams `0` the atoms' codes, `1` the parity's code, `2` the round counter, `3` the
systematic count, `4` the output). -/
def catW : WM 4 0 :=
  .seq (.whs 0 (copyBodyW 0 4))
    (.seq (.fwd 2) (.seq (.whs 2 (.seq (.fwd 3) (.fwd 2)))
      (.seq (.ifs 3 (.whs 1 (copyBodyW 1 4)) .skip) (emitW 4 false))))

def catCost (a p X : ℕ) : ℕ := (14 * a + 1) + 1 + (1 + 1 + ((5 * X + 1) + 1 + ((14 * p + 1 + 1) + 1 + 3)))

theorem catW_spec (a p rA rP rc : List Bool) (X sys : ℕ) (hrc : rc.getD 0 false = false) (σ : WState 4 0)
    (h0 : ∀ j, σ.sh j = 0) (hA : σ.st 0 = frame a ++ rA) (hP : σ.st 1 = frame p ++ rP)
    (hC : σ.st 2 = List.replicate (X + 1) true ++ rc) (hS : σ.st 3 = List.replicate sys true) (hO : σ.st 4 = []) :
    ∃ τ, WExec 0 catW σ τ (catCost a.length p.length X) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = σ.st 1 ∧
      τ.st 2 = σ.st 2 ∧ τ.st 3 = σ.st 3 ∧ τ.st 4 = frame (a ++ if X < sys then p else []) ∧ τ.cell = σ.cell := by
  -- the atoms' codes
  obtain ⟨σ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := copyLoop_spec 0 (0 : Fin 5) 4 (by decide) rA a [] σ
    (by rw [hA]; simp) (by rw [h0]; rfl) (by rw [h0, hO]; rfl)
  -- the counter
  obtain ⟨σ2, s2, n2, n2h, o2, v2, c2⟩ := fwd_facts 0 (2 : Fin 5) σ1
  have C1 := o1 2 (by decide) (by decide)
  obtain ⟨σ3, s3, e3, e3C, e3S, oth3, v3, c3⟩ := skipAlong_spec 0 (2 : Fin 5) 3 (by decide) rc hrc X [true] σ2
    (by rw [n2, C1.1, hC]; simp [List.replicate_succ]) (by rw [n2h, C1.2, h0]; rfl)
  have S1 := o1 3 (by decide) (by decide)
  have S2 := o2 3 (by decide)
  have hSh : σ3.sh 3 = X := by rw [e3S, S2.2, S1.2, h0]; simp
  have hSst : σ3.st 3 = List.replicate sys true := by rw [e3, S2.1, S1.1, hS]
  have hflag : wbit σ3 3 = decide (X < sys) := by
    simp only [wbit, hSst, hSh, readTapeBit]
    by_cases hX : X < sys
    · simp [hX, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    · simp [hX, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  -- the output stream after the atoms
  have O3st : σ3.st 4 = frameP a := by
    rw [e3, (o2 4 (by decide)).1, e1, hO]; simp
  have O3h : σ3.sh 4 = (σ3.st 4).length := by
    rw [oth3 4 (by decide) (by decide), (o2 4 (by decide)).2, e1h, e3, (o2 4 (by decide)).1]
  -- the parity's code, if systematic
  have P3st : σ3.st 1 = frame p ++ rP := by rw [e3, (o2 1 (by decide)).1, (o1 1 (by decide) (by decide)).1, hP]
  have P3h : σ3.sh 1 = 0 := by
    rw [oth3 1 (by decide) (by decide), (o2 1 (by decide)).2, (o1 1 (by decide) (by decide)).2, h0]
  have hpar : ∃ σ4, WExec 0 (.ifs 3 (.whs 1 (copyBodyW 1 4)) .skip) σ3 σ4 (14 * p.length + 1 + 1) ∧
      σ4.st 4 = frameP a ++ (if X < sys then frameP p else []) ∧ σ4.sh 4 = (σ4.st 4).length ∧
      (∀ j, j ≠ 4 → σ4.st j = σ3.st j) ∧ σ4.cell = σ3.cell := by
    by_cases hX : X < sys
    · obtain ⟨σ4, s4, e4, e4h, n4, -, o4, -, c4⟩ := copyLoop_spec 0 (1 : Fin 5) 4 (by decide) rP p [] σ3
        (by rw [P3st]; simp) (by rw [P3h]; rfl) O3h
      refine ⟨σ4, WExec.ifsT (by rw [hflag]; simp [hX]) s4, by rw [e4, O3st, if_pos hX], e4h, ?_, c4⟩
      intro j hj
      by_cases hj1 : j = 1
      · subst hj1; exact n4
      · exact (o4 j hj1 hj).1
    · refine ⟨σ3, WExec.mono (WExec.ifsF (by rw [hflag]; simp [hX]) (WExec.skip _)) (by omega),
        by rw [O3st, if_neg hX, List.append_nil], O3h, fun _ _ => rfl, rfl⟩
  obtain ⟨σ4, s4, e4, e4h, o4, c4⟩ := hpar
  obtain ⟨τ, s5, e5, -, o5, -, c5⟩ := emit_facts 0 (4 : Fin 5) false σ4 e4h
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) (by unfold catCost; omega),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(o5 0 (by decide)).1, o4 0 (by decide), e3, (o2 0 (by decide)).1, n1]
  · rw [(o5 1 (by decide)).1, o4 1 (by decide), P3st, hP]
  · rw [(o5 2 (by decide)).1, o4 2 (by decide), e3, n2, C1.1]
  · rw [(o5 3 (by decide)).1, o4 3 (by decide), hSst, hS]
  · rw [e5, e4, frame_eq_frameP, frameP_app]
    split_ifs <;> simp
  · rw [c5, c4, c3, c2, c1]

def σCat (A P C S : List Bool) : WState 4 0 := ⟨fun _ => 0, ![A, P, C, S, []], fun r => r.elim0, false⟩

/-- The carrier input's entry bank: the atoms' codes, the cell, the parity's code, the counter, the systematic
count, the (blank) output, the log. -/
def catIn (A P C S : List Bool) : Fin 7 → List Bool :=
  Fin.addCases (m := 4 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σCat A P C S)).A (fun _ => [])

theorem catIn_val (A P C S : List Bool) (j : Fin 7) :
    catIn A P C S j = if j.val = 0 then A else if j.val = 1 then [false] else if j.val = 2 then P else
      if j.val = 3 then C else if j.val = 4 then S else [] := by
  fin_cases j <;> rfl

/-- **The carrier input as a Step.** -/
theorem catStage (a p rA rP rc : List Bool) (X sys : ℕ) (hrc : rc.getD 0 false = false) :
    ∃ o : Fin 7 → List Bool,
      Step (Rewind.machine catW.toProg.compile) (2 * catCost a.length p.length X + 2) (fun _ => 0)
        (catIn (frame a ++ rA) (frame p ++ rP) (List.replicate (X + 1) true ++ rc) (List.replicate sys true))
        (fun _ => 0) o ∧
      o 0 = frame a ++ rA ∧ o 1 = [false] ∧ o 2 = frame p ++ rP ∧ o 3 = List.replicate (X + 1) true ++ rc ∧
      o 4 = List.replicate sys true ∧ o 5 = frame (a ++ if X < sys then p else []) := by
  set σ := σCat (frame a ++ rA) (frame p ++ rP) (List.replicate (X + 1) true ++ rc) (List.replicate sys true) with hσ
  obtain ⟨τ, hw, e0, e1, e2, e3, e4, ec⟩ := catW_spec a p rA rP rc X sys hrc σ (fun _ => rfl) rfl rfl rfl rfl rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 catW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 7) = Fin.castAdd 1 (0 : Fin 6) from rfl, ho]; exact e0
  · rw [show (1 : Fin 7) = Fin.castAdd 1 (1 : Fin 6) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 7) = Fin.castAdd 1 (2 : Fin 6) from rfl, ho]; exact e1
  · rw [show (3 : Fin 7) = Fin.castAdd 1 (3 : Fin 6) from rfl, ho]; exact e2
  · rw [show (4 : Fin 7) = Fin.castAdd 1 (4 : Fin 6) from rfl, ho]; exact e3
  · rw [show (5 : Fin 7) = Fin.castAdd 1 (5 : Fin 6) from rfl, ho]; exact e4

/-! ## The envelope bit -/

/-- **The envelope bit** (streams `0` the envelope stage's `frame [b]`, `1` the round counter, `2` the flags). -/
def efW : WM 2 0 :=
  .seq (.fwd 1) (.seq (.whs 1 (.seq (.fwd 2) (.fwd 1))) (.seq (.fwd 0) (.ifs 0 (emitW 2 true) (emitW 2 false))))

def efCost (X : ℕ) : ℕ := 1 + 1 + ((5 * X + 1) + 1 + (1 + 1 + (3 + 1)))

theorem efW_spec (b : Bool) (rE rc F : List Bool) (X : ℕ) (hrc : rc.getD 0 false = false) (hF : F.length = X)
    (σ : WState 2 0) (h0 : ∀ j, σ.sh j = 0) (hE : σ.st 0 = frame [b] ++ rE)
    (hC : σ.st 1 = List.replicate (X + 1) true ++ rc) (hFs : σ.st 2 = F) :
    ∃ τ, WExec 0 efW σ τ (efCost X) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = σ.st 1 ∧ τ.st 2 = F ++ [b] ∧
      τ.cell = σ.cell := by
  obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := fwd_facts 0 (1 : Fin 3) σ
  obtain ⟨σ2, s2, e2, e2C, e2S, oth2, v2, c2⟩ := skipAlong_spec 0 (1 : Fin 3) 2 (by decide) rc hrc X [true] σ1
    (by rw [n1, hC]; simp [List.replicate_succ]) (by rw [n1h, h0]; rfl)
  obtain ⟨σ3, s3, n3, n3h, o3, v3, c3⟩ := fwd_facts 0 (0 : Fin 3) σ2
  have E2 : σ2.st 0 = frame [b] ++ rE := by rw [e2, (o1 0 (by decide)).1, hE]
  have E2h : σ2.sh 0 = 0 := by rw [oth2 0 (by decide) (by decide), (o1 0 (by decide)).2, h0]
  have hbit : wbit σ3 0 = b := by
    simp only [wbit, n3, n3h, E2, E2h]; cases b <;> rfl
  have F3 : σ3.st 2 = F := by rw [(o3 2 (by decide)).1, e2, (o1 2 (by decide)).1, hFs]
  have F3h : σ3.sh 2 = (σ3.st 2).length := by
    rw [(o3 2 (by decide)).2, e2S, (o1 2 (by decide)).2, h0, F3, hF]; simp
  obtain ⟨τ, s4, e4, -, o4, -, c4⟩ := emit_facts 0 (2 : Fin 3) b σ3 F3h
  have s4' : WExec 0 (.ifs 0 (emitW 2 true) (emitW 2 false)) σ3 τ 4 := by
    cases b
    · exact WExec.ifsF hbit s4
    · exact WExec.ifsT hbit s4
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4'))) (by unfold efCost; omega), ?_, ?_, ?_, ?_⟩
  · rw [(o4 0 (by decide)).1, n3, E2, hE]
  · rw [(o4 1 (by decide)).1, (o3 1 (by decide)).1, e2, n1]
  · rw [e4, F3]
  · rw [c4, c3, c2, c1]

def σEf (E C F : List Bool) : WState 2 0 := ⟨fun _ => 0, ![E, C, F], fun r => r.elim0, false⟩

/-- The envelope bit's entry bank: the envelope output, the cell, the counter, the flags, the log. -/
def efIn (E C F : List Bool) : Fin 5 → List Bool :=
  Fin.addCases (m := 2 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σEf E C F)).A (fun _ => [])

theorem efIn_val (E C F : List Bool) (j : Fin 5) :
    efIn E C F j = if j.val = 0 then E else if j.val = 1 then [false] else if j.val = 2 then C else
      if j.val = 3 then F else [] := by
  fin_cases j <;> rfl

/-- **The envelope bit as a Step.** -/
theorem efStage (b : Bool) (rE rc F : List Bool) (X : ℕ) (hrc : rc.getD 0 false = false) (hF : F.length = X) :
    ∃ o : Fin 5 → List Bool,
      Step (Rewind.machine efW.toProg.compile) (2 * efCost X + 2) (fun _ => 0)
        (efIn (frame [b] ++ rE) (List.replicate (X + 1) true ++ rc) F) (fun _ => 0) o ∧
      o 0 = frame [b] ++ rE ∧ o 1 = [false] ∧ o 2 = List.replicate (X + 1) true ++ rc ∧ o 3 = F ++ [b] := by
  set σ := σEf (frame [b] ++ rE) (List.replicate (X + 1) true ++ rc) F with hσ
  obtain ⟨τ, hw, e0, e1, e2, ec⟩ := efW_spec b rE rc F X hrc hF σ (fun _ => rfl) rfl rfl rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 efW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 5) = Fin.castAdd 1 (0 : Fin 4) from rfl, ho]; exact e0
  · rw [show (1 : Fin 5) = Fin.castAdd 1 (1 : Fin 4) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 5) = Fin.castAdd 1 (2 : Fin 4) from rfl, ho]; exact e1
  · rw [show (3 : Fin 5) = Fin.castAdd 1 (3 : Fin 4) from rfl, ho]; exact e2

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldCat
