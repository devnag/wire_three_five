import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.UnionMachine.FrontKit

/-! # SEEDFIX C4 part: the front stage (the request's class mode, P3:3165-3175)

"The seeds a call fixes before its final pass" (P3:3165-3175) depend on the call's class mode (`samp:printable`'s sample
for SYM; for THR the fixed hash first, `filt:soft`). The front stage reads the mode bit of the request word
`natWord n ++ [mode] ++ …` from its framed input and writes it on its output: a register-free word program (four
streams: the request, the output, a unary count `S` of `natWord n`'s length prefix, a unary record `U` of the
request's head) skips the length prefix and the `L` value bits, reads the mode bit, and walks the request's head back
along `U`. **`front_run`**: `C4At.front_run`'s run, `Stage3Run frontS B req.word [] [modeBit req]`.

Paper quantity of the main type: the call's class mode `modeBit req`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Front
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes

abbrev FS := WState 3 0
abbrev FW := WM 3 0

/-- The front's word state: the request `fw` (head `h0`), the output, `S` and `U` with their heads. -/
def fst (fw : List Bool) (h0 : ℕ) (out S U : List Bool) (hS hU : ℕ) : FS :=
  ⟨![h0, 0, hS, hU], ![fw, out, S, U], Fin.elim0, false⟩

theorem write_rep (n : ℕ) (b : Bool) : writeTapeBit (List.replicate n b) n b = List.replicate (n + 1) b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, writeTapeBit, ih]

theorem write_mid' (pre rest : List Bool) (b x : Bool) :
    writeTapeBit (pre ++ b :: rest) pre.length x = pre ++ x :: rest := by
  rw [StablePartition.Workspace.write_boundary]; rfl

theorem frame_odd : ∀ (w : List Bool) (i : ℕ), readTapeBit (frame w) (2 * i + 1) = w.getD i false
  | [], i => by simp [frame, readTapeBit]
  | b :: w, 0 => by simp [frame, readTapeBit]
  | b :: w, i + 1 => by
    have := frame_odd w i
    simp only [readTapeBit] at this ⊢
    rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by ring]
    simpa [frame] using this

section Progs
variable (cap : ℕ)

/-- One step on the request, recorded on `U`. -/
def mvW : FW := .seq (.fwd 0) (.seq (.wr 3 true) (.fwd 3))

theorem mv_spec (fw out S : List Bool) (h0 hS u : ℕ) :
    WExec cap mvW (fst fw h0 out S (List.replicate u true) hS u)
      (fst fw (h0 + 1) out S (List.replicate (u + 1) true) hS (u + 1)) 5 := by
  have s1 := WExec.fwd (cap := cap) 0 (fst fw h0 out S (List.replicate u true) hS u)
  set σ1 := (fst fw h0 out S (List.replicate u true) hS u).seth 0
    ((fst fw h0 out S (List.replicate u true) hS u).sh 0 + 1) with hσ1
  have s2 := WExec.wr (cap := cap) 3 true σ1
  have e2 : writeTapeBit (σ1.st 3) (σ1.sh 3) true = List.replicate (u + 1) true := by
    simp only [σ1, fst, WState.seth_st, WState.seth_sh, Function.update_apply]
    simp [write_rep]
  rw [e2] at s2
  have s3 := WExec.fwd (cap := cap) 3 (σ1.sets 3 (List.replicate (u + 1) true))
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (le_refl _)
  apply WState.eq
  · funext i; fin_cases i <;> simp [σ1, fst, Function.update_apply]
  · funext i; fin_cases i <;> simp [σ1, fst, Function.update_apply]
  · funext r; exact r.elim0
  · rfl

/-- The length prefix: while the payload bit is set, count it on `S` and step two cells. -/
def p1W : FW := .whs 0 (.seq (.seq (.wr 2 true) (.fwd 2)) (.seq mvW mvW))

theorem p1_spec (w : List Bool) (L : ℕ) (hw : ∀ i < L, w.getD i false = true) (hL : w.getD L false = false) :
    ∀ i, i ≤ L → WExec cap p1W (fst (frame w) (2 * i + 1) [] (List.replicate i true) (List.replicate (2 * i + 1) true)
      i (2 * i + 1)) (fst (frame w) (2 * L + 1) [] (List.replicate L true) (List.replicate (2 * L + 1) true) L
        (2 * L + 1)) ((L - i) * 17 + 1)
  | i, hi => by
    by_cases hiL : i = L
    · subst hiL
      have hb : wbit (fst (frame w) (2 * i + 1) [] (List.replicate i true) (List.replicate (2 * i + 1) true) i
          (2 * i + 1)) 0 = false := by
        simp only [wbit, fst]; simpa using (frame_odd w i).trans hL
      exact WExec.mono (WExec.whsF hb) (by omega)
    · have hlt : i < L := by omega
      have hb : wbit (fst (frame w) (2 * i + 1) [] (List.replicate i true) (List.replicate (2 * i + 1) true) i
          (2 * i + 1)) 0 = true := by
        simp only [wbit, fst]; simpa using (frame_odd w i).trans (hw i hlt)
      set σ := fst (frame w) (2 * i + 1) [] (List.replicate i true) (List.replicate (2 * i + 1) true) i (2 * i + 1)
      have t1 := WExec.wr (cap := cap) 2 true σ
      have e1 : writeTapeBit (σ.st 2) (σ.sh 2) true = List.replicate (i + 1) true := by simp [σ, fst, write_rep]
      rw [e1] at t1
      have t2 := WExec.fwd (cap := cap) 2 (σ.sets 2 (List.replicate (i + 1) true))
      have e2 : (σ.sets 2 (List.replicate (i + 1) true)).seth 2 ((σ.sets 2 (List.replicate (i + 1) true)).sh 2 + 1) =
          fst (frame w) (2 * i + 1) [] (List.replicate (i + 1) true) (List.replicate (2 * i + 1) true) (i + 1)
            (2 * i + 1) := by
        apply WState.eq
        · funext j; fin_cases j <;> simp [σ, fst, Function.update_apply]
        · funext j; fin_cases j <;> simp [σ, fst, Function.update_apply]
        · funext r; exact r.elim0
        · rfl
      rw [e2] at t2
      have t3 := mv_spec cap (frame w) [] (List.replicate (i + 1) true) (2 * i + 1) (i + 1) (2 * i + 1)
      have t4 := mv_spec cap (frame w) [] (List.replicate (i + 1) true) (2 * i + 1 + 1) (i + 1) (2 * i + 1 + 1)
      have ih := p1_spec w L hw hL (i + 1) (by omega)
      have e3 : 2 * i + 1 + 1 + 1 = 2 * (i + 1) + 1 := by ring
      rw [e3] at t4
      have hw := WExec.whsT hb (WExec.seq (WExec.seq t1 t2) (WExec.seq t3 t4)) ih
      refine WExec.cast cap hw rfl ?_
      have : L - i = (L - (i + 1)) + 1 := by omega
      rw [this, Nat.add_mul]; simp only [Nat.one_mul]; omega
  termination_by i => L - i

/-- Skip `L` pairs along `S`, clearing it from its last one back to cell `0`. -/
def p3LoopW : FW := .whs 2 (.seq (.wr 2 false) (.seq (.bwd 2) (.seq mvW mvW)))

theorem p3Loop_spec (fw : List Bool) :
    ∀ (j r h0 : ℕ), WExec cap p3LoopW (fst fw h0 [] (List.replicate (j + 1) true ++ List.replicate r false)
      (List.replicate h0 true) j h0) (fst fw (h0 + 2 * (j + 1)) [] (List.replicate (j + 1 + r) false)
        (List.replicate (h0 + 2 * (j + 1)) true) 0 (h0 + 2 * (j + 1))) ((j + 1) * 17 + 1)
  | 0, r, h0 => by
    set σ := fst fw h0 [] (List.replicate (0 + 1) true ++ List.replicate r false) (List.replicate h0 true) 0 h0
    have hb : wbit σ 2 = true := by simp [σ, wbit, fst, readTapeBit]
    have t1 := WExec.wr (cap := cap) 2 false σ
    have e1 : writeTapeBit (σ.st 2) (σ.sh 2) false = List.replicate (1 + r) false := by
      simp [σ, fst, writeTapeBit, List.replicate_succ, Nat.add_comm]
    rw [e1] at t1
    have t2 := WExec.bwd (cap := cap) 2 (σ.sets 2 (List.replicate (1 + r) false))
    have e2 : (σ.sets 2 (List.replicate (1 + r) false)).seth 2 ((σ.sets 2 (List.replicate (1 + r) false)).sh 2 - 1) =
        fst fw h0 [] (List.replicate (1 + r) false) (List.replicate h0 true) 0 h0 := by
      apply WState.eq
      · funext j; fin_cases j <;> simp [σ, fst, Function.update_apply]
      · funext j; fin_cases j <;> simp [σ, fst, Function.update_apply]
      · funext r; exact r.elim0
      · rfl
    rw [e2] at t2
    have t3 := mv_spec cap fw [] (List.replicate (1 + r) false) h0 0 h0
    have t4 := mv_spec cap fw [] (List.replicate (1 + r) false) (h0 + 1) 0 (h0 + 1)
    have hb2 : wbit (fst fw (h0 + 1 + 1) [] (List.replicate (1 + r) false) (List.replicate (h0 + 1 + 1) true) 0
        (h0 + 1 + 1)) 2 = false := by
      simp [wbit, fst, readTapeBit, List.replicate_succ, Nat.add_comm 1 r]
    have hw := WExec.whsT hb (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 t4))) (WExec.whsF hb2)
    refine WExec.cast cap hw ?_ ?_
    · rw [show h0 + 2 * (0 + 1) = h0 + 1 + 1 by ring, show 0 + 1 + r = 1 + r by ring]
    · omega
  | j + 1, r, h0 => by
    set σ := fst fw h0 [] (List.replicate (j + 1 + 1) true ++ List.replicate r false) (List.replicate h0 true) (j + 1) h0
    have hb : wbit σ 2 = true := by
      show (List.replicate (j + 1 + 1) true ++ List.replicate r false).getD (j + 1) false = true
      rw [List.getD_append _ _ _ _ (by simp)]; simp
    have t1 := WExec.wr (cap := cap) 2 false σ
    have e1 : writeTapeBit (σ.st 2) (σ.sh 2) false = List.replicate (j + 1) true ++ List.replicate (r + 1) false := by
      simp only [σ, fst]
      simp only [Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.tail_cons]
      have h1 : List.replicate (j + 1 + 1) true ++ List.replicate r false =
          List.replicate (j + 1) true ++ true :: List.replicate r false := by
        rw [List.replicate_succ' (n := j + 1), List.append_assoc]; rfl
      rw [h1]
      have := write_mid' (List.replicate (j + 1) true) (List.replicate r false) true false
      rw [List.length_replicate] at this
      rw [this]; rfl
    rw [e1] at t1
    have t2 := WExec.bwd (cap := cap) 2 (σ.sets 2 (List.replicate (j + 1) true ++ List.replicate (r + 1) false))
    have e2 : (σ.sets 2 (List.replicate (j + 1) true ++ List.replicate (r + 1) false)).seth 2
        ((σ.sets 2 (List.replicate (j + 1) true ++ List.replicate (r + 1) false)).sh 2 - 1) =
        fst fw h0 [] (List.replicate (j + 1) true ++ List.replicate (r + 1) false) (List.replicate h0 true) j h0 := by
      apply WState.eq
      · funext i; fin_cases i <;> simp [σ, fst, Function.update_apply]
      · funext i; fin_cases i <;> simp [σ, fst, Function.update_apply]
      · funext r; exact r.elim0
      · rfl
    rw [e2] at t2
    have t3 := mv_spec cap fw [] (List.replicate (j + 1) true ++ List.replicate (r + 1) false) h0 j h0
    have t4 := mv_spec cap fw [] (List.replicate (j + 1) true ++ List.replicate (r + 1) false) (h0 + 1) j (h0 + 1)
    have ih := p3Loop_spec fw j (r + 1) (h0 + 1 + 1)
    have hw := WExec.whsT hb (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 t4))) ih
    refine WExec.cast cap hw ?_ ?_
    · rw [show h0 + 1 + 1 + 2 * (j + 1) = h0 + 2 * (j + 1 + 1) by ring, show j + 1 + (r + 1) = j + 1 + 1 + r by ring]
    · rw [Nat.add_mul (j + 1) 1 17]; omega

/-- Walk the request's head back along `U`, clearing `U`. -/
def p5LoopW : FW := .whs 3 (.seq (.wr 3 false) (.seq (.bwd 3) (.bwd 0)))

theorem p5Loop_spec (fw out S : List Bool) :
    ∀ (j r : ℕ), WExec cap p5LoopW (fst fw (j + 1) out S (List.replicate (j + 1) true ++ List.replicate r false) 0 j)
      (fst fw 0 out S (List.replicate (j + 1 + r) false) 0 0) ((j + 1) * 7 + 1)
  | 0, r => by
    set σ := fst fw (0 + 1) out S (List.replicate (0 + 1) true ++ List.replicate r false) 0 0
    have hb : wbit σ 3 = true := by simp [σ, wbit, fst, readTapeBit]
    have t1 := WExec.wr (cap := cap) 3 false σ
    have e1 : writeTapeBit (σ.st 3) (σ.sh 3) false = List.replicate (1 + r) false := by
      simp [σ, fst, writeTapeBit, List.replicate_succ, Nat.add_comm]
    rw [e1] at t1
    have t2 := WExec.bwd (cap := cap) 3 (σ.sets 3 (List.replicate (1 + r) false))
    have t3 := WExec.bwd (cap := cap) 0 ((σ.sets 3 (List.replicate (1 + r) false)).seth 3
      ((σ.sets 3 (List.replicate (1 + r) false)).sh 3 - 1))
    have e3 : ((σ.sets 3 (List.replicate (1 + r) false)).seth 3 ((σ.sets 3 (List.replicate (1 + r) false)).sh 3 - 1)).seth
        0 (((σ.sets 3 (List.replicate (1 + r) false)).seth 3 ((σ.sets 3 (List.replicate (1 + r) false)).sh 3 - 1)).sh 0
          - 1) = fst fw 0 out S (List.replicate (0 + 1 + r) false) 0 0 := by
      apply WState.eq
      · funext i; fin_cases i <;> simp [σ, fst, Function.update_apply]
      · funext i; fin_cases i <;> simp [σ, fst, Function.update_apply, Nat.add_comm]
      · funext r; exact r.elim0
      · rfl
    rw [e3] at t3
    have hb2 : wbit (fst fw 0 out S (List.replicate (0 + 1 + r) false) 0 0) 3 = false := by
      simp [wbit, fst, readTapeBit, List.replicate_succ]
    exact WExec.cast cap (WExec.whsT hb (WExec.seq t1 (WExec.seq t2 t3)) (WExec.whsF hb2)) rfl (by omega)
  | j + 1, r => by
    set σ := fst fw (j + 1 + 1) out S (List.replicate (j + 1 + 1) true ++ List.replicate r false) 0 (j + 1)
    have hb : wbit σ 3 = true := by
      show (List.replicate (j + 1 + 1) true ++ List.replicate r false).getD (j + 1) false = true
      rw [List.getD_append _ _ _ _ (by simp)]; simp
    have t1 := WExec.wr (cap := cap) 3 false σ
    have e1 : writeTapeBit (σ.st 3) (σ.sh 3) false = List.replicate (j + 1) true ++ List.replicate (r + 1) false := by
      simp only [σ, fst]
      simp only [Matrix.cons_val_three, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_zero, Matrix.tail_cons]
      have h1 : List.replicate (j + 1 + 1) true ++ List.replicate r false =
          List.replicate (j + 1) true ++ true :: List.replicate r false := by
        rw [List.replicate_succ' (n := j + 1), List.append_assoc]; rfl
      rw [h1]
      have := write_mid' (List.replicate (j + 1) true) (List.replicate r false) true false
      rw [List.length_replicate] at this
      rw [this]; rfl
    rw [e1] at t1
    have t2 := WExec.bwd (cap := cap) 3 (σ.sets 3 (List.replicate (j + 1) true ++ List.replicate (r + 1) false))
    have t3 := WExec.bwd (cap := cap) 0 ((σ.sets 3 (List.replicate (j + 1) true ++ List.replicate (r + 1) false)).seth 3
      ((σ.sets 3 (List.replicate (j + 1) true ++ List.replicate (r + 1) false)).sh 3 - 1))
    have e3 : ((σ.sets 3 (List.replicate (j + 1) true ++ List.replicate (r + 1) false)).seth 3
        ((σ.sets 3 (List.replicate (j + 1) true ++ List.replicate (r + 1) false)).sh 3 - 1)).seth 0
        (((σ.sets 3 (List.replicate (j + 1) true ++ List.replicate (r + 1) false)).seth 3
          ((σ.sets 3 (List.replicate (j + 1) true ++ List.replicate (r + 1) false)).sh 3 - 1)).sh 0 - 1) =
        fst fw (j + 1) out S (List.replicate (j + 1) true ++ List.replicate (r + 1) false) 0 j := by
      apply WState.eq
      · funext i; fin_cases i <;> simp [σ, fst, Function.update_apply]
      · funext i; fin_cases i <;> simp [σ, fst, Function.update_apply]
      · funext r; exact r.elim0
      · rfl
    rw [e3] at t3
    have ih := p5Loop_spec fw out S j (r + 1)
    have hw := WExec.whsT hb (WExec.seq t1 (WExec.seq t2 t3)) ih
    refine WExec.cast cap hw ?_ ?_
    · rw [show j + 1 + (r + 1) = j + 1 + 1 + r by ring]
    · rw [Nat.add_mul (j + 1) 1 7]; omega

end Progs

section Front
variable (cap : ℕ)

def p3W : FW := .seq (.bwd 2) p3LoopW
def p4W : FW := .ifs 0 (.wr 1 true) (.wr 1 false)
def p5W : FW := .seq (.bwd 3) p5LoopW

/-- **The front's word program.** -/
def frontW : FW := .seq mvW (.seq p1W (.seq (.seq mvW mvW) (.seq p3W (.seq p4W p5W))))

theorem p3_spec (fw : List Bool) (L : ℕ) :
    ∃ c, c ≤ 17 * L + 3 ∧ WExec cap p3W (fst fw (2 * L + 3) [] (List.replicate L true) (List.replicate (2 * L + 3) true)
      L (2 * L + 3)) (fst fw (4 * L + 3) [] (List.replicate L false) (List.replicate (4 * L + 3) true) 0 (4 * L + 3)) c := by
  have t1 := WExec.bwd (cap := cap) 2
    (fst fw (2 * L + 3) [] (List.replicate L true) (List.replicate (2 * L + 3) true) L (2 * L + 3))
  cases L with
  | zero =>
    have hb : wbit ((fst fw (2 * 0 + 3) [] (List.replicate 0 true) (List.replicate (2 * 0 + 3) true) 0 (2 * 0 + 3)).seth 2
        ((fst fw (2 * 0 + 3) [] (List.replicate 0 true) (List.replicate (2 * 0 + 3) true) 0 (2 * 0 + 3)).sh 2 - 1)) 2
        = false := by
      simp [wbit, fst, readTapeBit]
    refine ⟨_, ?_, WExec.cast cap (WExec.seq t1 (WExec.whsF (P := WM.seq (WM.wr 2 false) (WM.seq (WM.bwd 2)
      (WM.seq mvW mvW))) hb)) ?_ (le_refl _)⟩
    · omega
    · apply WState.eq
      · funext i; fin_cases i <;> simp [fst, Function.update_apply]
      · funext i; fin_cases i <;> simp [fst, Function.update_apply]
      · funext r; exact r.elim0
      · rfl
  | succ j =>
    have e1 : (fst fw (2 * (j + 1) + 3) [] (List.replicate (j + 1) true) (List.replicate (2 * (j + 1) + 3) true) (j + 1)
        (2 * (j + 1) + 3)).seth 2 ((fst fw (2 * (j + 1) + 3) [] (List.replicate (j + 1) true)
          (List.replicate (2 * (j + 1) + 3) true) (j + 1) (2 * (j + 1) + 3)).sh 2 - 1) =
        fst fw (2 * (j + 1) + 3) [] (List.replicate (j + 1) true ++ List.replicate 0 false)
          (List.replicate (2 * (j + 1) + 3) true) j (2 * (j + 1) + 3) := by
      apply WState.eq
      · funext i; fin_cases i <;> simp [fst, Function.update_apply]
      · funext i; fin_cases i <;> simp [fst, Function.update_apply]
      · funext r; exact r.elim0
      · rfl
    rw [e1] at t1
    have t2 := p3Loop_spec cap fw j 0 (2 * (j + 1) + 3)
    refine ⟨_, ?_, WExec.cast cap (WExec.seq t1 t2) ?_ (le_refl _)⟩
    · omega
    · rw [show 2 * (j + 1) + 3 + 2 * (j + 1) = 4 * (j + 1) + 3 by ring, show j + 1 + 0 = j + 1 by ring]

theorem p5_spec (fw out S : List Bool) (h : ℕ) :
    ∃ c, c ≤ 7 * h + 10 ∧ WExec cap p5W (fst fw (h + 1) out S (List.replicate (h + 1) true) 0 (h + 1))
      (fst fw 0 out S (List.replicate (h + 1) false) 0 0) c := by
  have t1 := WExec.bwd (cap := cap) 3 (fst fw (h + 1) out S (List.replicate (h + 1) true) 0 (h + 1))
  have e1 : (fst fw (h + 1) out S (List.replicate (h + 1) true) 0 (h + 1)).seth 3
      ((fst fw (h + 1) out S (List.replicate (h + 1) true) 0 (h + 1)).sh 3 - 1) =
      fst fw (h + 1) out S (List.replicate (h + 1) true ++ List.replicate 0 false) 0 h := by
    apply WState.eq
    · funext i; fin_cases i <;> simp [fst, Function.update_apply]
    · funext i; fin_cases i <;> simp [fst, Function.update_apply]
    · funext r; exact r.elim0
    · rfl
  rw [e1] at t1
  have t2 := p5Loop_spec cap fw out S h 0
  exact ⟨_, by omega, WExec.seq t1 t2⟩

theorem frontW_spec (w : List Bool) (L : ℕ) (b : Bool) (hw : ∀ i < L, w.getD i false = true)
    (hL : w.getD L false = false) (hb : w.getD (2 * L + 1) false = b) :
    ∃ c, c ≤ 70 * L + 60 ∧ WExec cap frontW (fst (frame w) 0 [] [] [] 0 0)
      (fst (frame w) 0 [b] (List.replicate L false) (List.replicate (4 * L + 3) false) 0 0) c := by
  have t1 := mv_spec cap (frame w) [] [] 0 0 0
  have t2 := p1_spec cap w L hw hL 0 (Nat.zero_le _)
  have t3 := mv_spec cap (frame w) [] (List.replicate L true) (2 * L + 1) L (2 * L + 1)
  have t4 := mv_spec cap (frame w) [] (List.replicate L true) (2 * L + 1 + 1) L (2 * L + 1 + 1)
  obtain ⟨c5, hc5, t5⟩ := p3_spec cap (frame w) L
  have hbit : wbit (fst (frame w) (4 * L + 3) [] (List.replicate L false) (List.replicate (4 * L + 3) true) 0
      (4 * L + 3)) 0 = b := by
    show readTapeBit (frame w) (4 * L + 3) = b
    rw [show 4 * L + 3 = 2 * (2 * L + 1) + 1 by ring, frame_odd, hb]
  have t6 : WExec cap p4W (fst (frame w) (4 * L + 3) [] (List.replicate L false) (List.replicate (4 * L + 3) true) 0
      (4 * L + 3)) (fst (frame w) (4 * L + 3) [b] (List.replicate L false) (List.replicate (4 * L + 3) true) 0
        (4 * L + 3)) 2 := by
    cases b
    · refine WExec.cast cap (WExec.ifsF (P := WM.wr 1 true) hbit (WExec.wr 1 false _)) ?_ (le_refl _)
      apply WState.eq
      · rfl
      · funext i; fin_cases i <;> simp [fst, Function.update_apply, writeTapeBit]
      · funext r; exact r.elim0
      · rfl
    · refine WExec.cast cap (WExec.ifsT (Q := WM.wr 1 false) hbit (WExec.wr 1 true _)) ?_ (le_refl _)
      apply WState.eq
      · rfl
      · funext i; fin_cases i <;> simp [fst, Function.update_apply, writeTapeBit]
      · funext r; exact r.elim0
      · rfl
  obtain ⟨c7, hc7, t7⟩ := p5_spec cap (frame w) [b] (List.replicate L false) (4 * L + 2)
  have e0 : fst (frame w) (0 + 1) [] [] (List.replicate (0 + 1) true) 0 (0 + 1) =
      fst (frame w) (2 * 0 + 1) [] (List.replicate 0 true) (List.replicate (2 * 0 + 1) true) 0 (2 * 0 + 1) := rfl
  rw [e0] at t1
  have e3 : 2 * L + 1 + 1 + 1 = 2 * L + 3 := by ring
  rw [e3] at t4
  rw [show 4 * L + 2 + 1 = 4 * L + 3 by ring] at t7
  exact ⟨_, by omega, WExec.seq t1 (WExec.seq t2 (WExec.seq (WExec.seq t3 t4) (WExec.seq t5 (WExec.seq t6 t7))))⟩

end Front

section Stage
variable (cap : ℕ)

/-- The word program's slots on the stage: the request, the cell, the output, `S`, `U`. -/
def slF : Fin 5 → Fin 6 := ![0, 3, 2, 4, 5]

theorem slF_inj : Function.Injective slF := by decide

/-- **The front stage's machine**: the cell tape `[F]`, then the word program. -/
noncomputable def frontM := Composition.machine (UnionMachine.FrontKit.cellP (3 : Fin 6)).compile
  (RecoveryFocus.machine slF frontW.toProg.compile)

/-- **The front stage.** -/
noncomputable def frontS : Stage3 := ⟨3, _, frontM⟩

theorem ready_mono {t s : ℕ} {p : Machine t s} {n m : ℕ} {A A' : Fin t → List Bool} (h : ClockJoin.ReadyRun p n A A')
    (hnm : n ≤ m) : ClockJoin.ReadyRun p m A A' := by
  obtain ⟨r, hr, ht, hh, _⟩ := h
  exact UnionMachine.FrontKit.ready_of_step ((Step.of_run hr (funext hh) ht).enlarge hnm)

theorem front_stage (w : List Bool) (L : ℕ) (b : Bool) (hw : ∀ i < L, w.getD i false = true)
    (hL : w.getD L false = false) (hb : w.getD (2 * L + 1) false = b) (B : ℕ) (hB : 70 * L + 64 ≤ B) :
    Stage3Run frontS B w [] [b] := by
  obtain ⟨c, hc, hw1⟩ := frontW_spec 0 w L b hw hL hb
  have hr := UnionMachine.FrontKit.wm_ready frontW 0 c _ _ hw1 (fun i => by fin_cases i <;> rfl) (fun r => r.elim0)
    (fun i => by fin_cases i <;> rfl) (fun r => r.elim0)
  set A := stageIn 3 w [] with hA
  have r1 := UnionMachine.FrontKit.cell_ready (3 : Fin 6) A rfl
  have r2 := ClockJoin.ReadyRun.focus hr slF slF_inj (Function.update A 3 [false]) (fun j => by
    fin_cases j <;> rfl)
  have r := ClockJoin.join _ _ 1 c _ _ _ r1 r2
  have hout : RecoveryRootRound.install slF (Function.update A 3 [false])
      (wenc 0 (fst (frame w) 0 [b] (List.replicate L false) (List.replicate (4 * L + 3) false) 0 0)).A =
      stageOut 3 w [] [b] ![[false], List.replicate L false, List.replicate (4 * L + 3) false] := by
    funext i
    fin_cases i
    · rw [show (⟨0, by omega⟩ : Fin 6) = slF 0 from rfl, RecoveryRootRound.install_slot slF slF_inj]; rfl
    · rw [RecoveryRootRound.install_other slF _ _ _ (by intro j; fin_cases j <;> decide)]; rfl
    · rw [show (⟨2, by omega⟩ : Fin 6) = slF 2 from rfl, RecoveryRootRound.install_slot slF slF_inj]; rfl
    · rw [show (⟨3, by omega⟩ : Fin 6) = slF 1 from rfl, RecoveryRootRound.install_slot slF slF_inj]; rfl
    · rw [show (⟨4, by omega⟩ : Fin 6) = slF 3 from rfl, RecoveryRootRound.install_slot slF slF_inj]; rfl
    · rw [show (⟨5, by omega⟩ : Fin 6) = slF 4 from rfl, RecoveryRootRound.install_slot slF slF_inj]; rfl
  rw [hout] at r
  refine ⟨![[false], List.replicate L false, List.replicate (4 * L + 3) false], ?_, ?_⟩
  · intro j
    fin_cases j
    · show ([false] : List Bool).length ≤ B; simp; omega
    · show (List.replicate L false).length ≤ B; simp; omega
    · show (List.replicate (4 * L + 3) false).length ≤ B; simp; omega
  · exact ready_mono r (by omega)

end Stage

section Req

theorem natWord_shape (n : ℕ) : ∃ L f, RepairRepresentation.natWord n = List.replicate L true ++ false :: f ∧
    f.length = L := ⟨_, _, rfl, List.length_ofFn⟩

/-- **The front stage's run on a request**: the mode bit, within any budget above `70·|req.word| + 64`. -/
theorem front_req (req : PrimRequest) (B : ℕ) (hB : 70 * req.word.length + 64 ≤ B) :
    Stage3Run frontS B req.word [] [modeBit req] := by
  obtain ⟨L, f, hn, hf⟩ := natWord_shape req.n
  have hw : req.word = List.replicate L true ++ false :: (f ++ modeBit req :: (RepairRepresentation.natWord req.a ++
      (List.ofFn fun i => RepairRepresentation.natWord (req.mode.code (req.circuits i))).flatten ++
      RepairRepresentation.natListWord (req.carriers.map Stars.Carrier.code) ++
      RepairRepresentation.natListWord req.translation)) := by
    unfold PrimRequest.word modeBit
    rw [hn]
    simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
    rfl
  have hlen : L ≤ req.word.length := by rw [hw]; simp
  refine front_stage req.word L (modeBit req) (fun i hi => ?_) ?_ ?_ B (by omega)
  · rw [hw, List.getD_append _ _ _ _ (by simp; omega)]; simp [hi]
  · rw [hw, List.getD_append_right _ _ _ _ (by simp)]; simp
  · rw [hw, List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_replicate]
    rw [show 2 * L + 1 - L = L + 1 by omega, List.getD_cons_succ, List.getD_append_right _ _ _ _ (by omega), hf,
      Nat.sub_self, List.getD_cons_zero]

end Req

end NearCubicWires.WireExponent3_5.PrimT.C4Front
