import Proof.Wire_3_5.Primitive.Writers.ThrData2

/-! # thrStage4U, part 4: the hash numbers written at the head of the data word

P3:2543-2558, 2596-2604, 2150-2157, 2220-2231 (the THR numbers: "the numbers at fixed positions first"): the data
word is `dataWord (hashNums ++ thrCounts) = [0] ++ marks (unaryList hashNums) ++ marks (unaryList thrCounts) ++ [0]`. A
register program on a small layout (the output stream `0`, the sixteen unary numbers on streams `1 … 16`, the data
stage's sixteen registers) writes the leading `0` and `marks (unaryList hashNums)`; the data stage's own collection,
without its leading `0`, appends the counts and the closing `0` (part 5):

* `asethG`, `emitUG`, **`emitUG_spec`** (a unary stream's marks, any layout);
* `emitsW`, `emitsCost`, **`emits_spec`** (a list of unary streams in order);
* `hL` (16 streams), `qhW`, `qhCost`, **`qh_spec`**: stream `0` holds `false :: marks (unaryList cs)`, head at its end.

Paper quantities of the main type: the hash numbers in unary (`unaryList hashNums`, the data word's first part). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Gen
variable {ns nr : ℕ} (cap : ℕ)

theorem asethG (O S : Fin (ns + 1)) (OP : Fin nr) (hS : S ≠ O) (x : WState ns nr) (k : ℕ) (u : List Bool) :
    appendO (x.seth S k) O OP u = (appendO x O OP u).seth S k := by
  apply WState.eq
  · funext j
    by_cases hjS : j = S
    · subst hjS; simp [Function.update_apply, hS]
    · by_cases hjO : j = O
      · subst hjO; simp [Function.update_apply, Ne.symm hS]
      · simp [Function.update_apply, hjS, hjO]
  · funext j; simp
  · funext r; simp
  · simp

/-- A unary stream's marks onto the output stream `O`. -/
def emitUG (O S : Fin (ns + 1)) (OP : Fin nr) : WM ns nr := .whs S (.seq (emitPair O OP true) (.fwd S))

theorem emitUG_spec (O S : Fin (ns + 1)) (OP : Fin nr) (hS : S ≠ O) (c : ℕ) (σ : WState ns nr)
    (hst : σ.st S = List.replicate c true) (hsh : σ.sh S = 0) (ho : σ.sh O = (σ.st O).length)
    (hc : σ.val OP + 2 * c ≤ cap) :
    WExec cap (emitUG O S OP) σ ((appendO σ O OP (marks (List.replicate c true))).seth S c) (c * 19 + 1) := by
  set T : ℕ → WState ns nr := fun k => (appendO σ O OP (marks (List.replicate k true))).seth S k with hT
  have tst : ∀ k, (T k).st S = List.replicate c true := fun k => by
    simp only [hT, WState.seth_st, appendO_st, Function.update_apply, if_neg hS, hst]
  have tsh : ∀ k, (T k).sh S = k := fun k => by
    simp [hT]
  have l := whsLoop cap S (.seq (emitPair O OP true) (.fwd S)) 17 c T
    (fun k hk => by simp only [wbit, tst, tsh, rep_read]; simp [hk])
    (by simp only [wbit, tst, tsh, rep_read]; simp)
    (fun k hk => by
      have hml := RepairOrdinary.Streaming.marks_length (List.replicate k true)
      have h1 := emitPair_spec cap O OP true (T k)
        (by simp [hT, Function.update_apply, Ne.symm hS, ho])
        (by simp [hT] at hml ⊢; omega)
      have h2 := WExec.fwd (cap := cap) S (appendO (T k) O OP [true, true])
      refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
      have e1 : appendO (T k) O OP [true, true] =
          (appendO σ O OP (marks (List.replicate (k + 1) true))).seth S k := by
        rw [hT]
        dsimp only
        rw [asethG O S OP hS, appendO_append, marks_rep_succ]
      rw [e1]
      simp [FinalPass.Tm.wseth_seth, hT])
  have e0 : T 0 = σ := by
    simp only [hT, List.replicate_zero]
    rw [show marks ([] : List Bool) = [] from rfl, appendO_nil, ← hsh, FinalPass.Tm.wseth_same]
  rw [e0] at l
  exact WExec.mono l (by nlinarith)

/-- The unary streams `l` in order, each followed by the separator. -/
def emitsW (O : Fin (ns + 1)) (OP : Fin nr) : List (Fin (ns + 1)) → WM ns nr
  | [] => .skip
  | S :: l => .seq (.seq (emitUG O S OP) (emitPair O OP false)) (emitsW O OP l)

def emitsCost : List ℕ → ℕ
  | [] => 0
  | c :: cs => c * 19 + 1 + 1 + 15 + 1 + emitsCost cs

theorem emits_spec (O : Fin (ns + 1)) (OP : Fin nr) : ∀ (l : List (Fin (ns + 1))) (cs : List ℕ) (σ : WState ns nr),
    l.length = cs.length → (∀ S ∈ l, S ≠ O) → l.Nodup →
    (∀ i (h : i < l.length) (hc : i < cs.length), σ.st (l.get ⟨i, h⟩) = List.replicate (cs.get ⟨i, hc⟩) true ∧
      σ.sh (l.get ⟨i, h⟩) = 0) →
    σ.sh O = (σ.st O).length → σ.val OP + 2 * (unaryList cs).length ≤ cap →
    ∃ τ : WState ns nr, WExec cap (emitsW O OP l) σ τ (emitsCost cs) ∧
      τ.st O = σ.st O ++ marks (unaryList cs) ∧ τ.sh O = (τ.st O).length ∧
      τ.val OP = σ.val OP + 2 * (unaryList cs).length ∧
      (∀ s, s ≠ O → τ.st s = σ.st s) ∧ (∀ r, r ≠ OP → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  intro l
  induction l with
  | nil =>
    intro cs σ hlen _ _ _ ho _
    have hc0 : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst hc0
    exact ⟨σ, WExec.skip σ, by simp [unaryList, marks], ho, by simp [unaryList], fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  | cons S l ih =>
    intro cs σ hlen hno hnd hst ho hcap
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have hSO : S ≠ O := hno S (by simp)
      have hnd' := List.nodup_cons.mp hnd
      obtain ⟨h0st, h0sh⟩ := hst 0 (by simp) (by simp)
      simp only [List.get_eq_getElem, List.getElem_cons_zero] at h0st h0sh
      have hml := RepairOrdinary.Streaming.marks_length (List.replicate c true)
      have hu : (unaryList (c :: cs)).length = c + 1 + (unaryList cs).length := by
        rw [unaryList_cons]; simp; omega
      have e1 := emitUG_spec cap O S OP hSO c σ h0st h0sh ho (by rw [hu] at hcap; omega)
      set σ1 := (appendO σ O OP (marks (List.replicate c true))).seth S c with hσ1
      have e2 := emitPair_spec cap O OP false σ1
        (by simp [hσ1, Function.update_apply, Ne.symm hSO, ho])
        (by simp [hσ1] at hml ⊢; rw [hu] at hcap; omega)
      set σ2 := appendO σ1 O OP [true, false] with hσ2
      have st2 : ∀ s, s ≠ O → s ≠ S → σ2.st s = σ.st s := fun s a b => by
        simp [hσ2, hσ1, Function.update_apply, a]
      have sh2 : ∀ s, s ≠ O → s ≠ S → σ2.sh s = σ.sh s := fun s a b => by
        simp [hσ2, hσ1, Function.update_apply, a, b]
      obtain ⟨τ, q, a1, b1, c1, d1, f1, g1⟩ := ih cs σ2 (by simpa using hlen) (fun S' hS' => hno S' (by simp [hS']))
        hnd'.2
        (fun i h hc => by
          have hne : l.get ⟨i, h⟩ ≠ S := fun e => hnd'.1 (e ▸ List.get_mem l ⟨i, h⟩)
          have hneO : l.get ⟨i, h⟩ ≠ O := hno _ (by simp [List.get_mem])
          obtain ⟨x1, x2⟩ := hst (i + 1) (by simp; omega) (by simp; omega)
          simp only [List.get_eq_getElem, List.getElem_cons_succ] at x1 x2
          refine ⟨?_, ?_⟩
          · rw [st2 _ hneO hne]; simpa using x1
          · rw [sh2 _ hneO hne]; simpa using x2)
        (by simp [hσ2, hσ1, Function.update_apply, Ne.symm hSO, ho]; simp at hml; omega)
        (by simp [hσ2, hσ1] at hml ⊢; rw [hu] at hcap; omega)
      refine ⟨τ, WExec.cast cap (WExec.seq (WExec.seq e1 e2) q) rfl (by simp only [emitsCost]; omega), ?_, b1, ?_, ?_, ?_, ?_⟩
      · rw [a1, unaryList_cons, marks_append, marks_append]
        simp [hσ2, hσ1, Function.update_apply, Ne.symm hSO, List.append_assoc]
        rfl
      · rw [c1, hu]; simp [hσ2, hσ1]; omega
      · intro s hs
        rw [d1 s hs]
        by_cases hsS : s = S
        · subst hsS; simp [hσ2, hσ1, Function.update_apply, hs]
        · exact st2 s hs hsS
      · intro r hr
        rw [f1 r hr]; simp [hσ2, hσ1, Function.update_apply, hr]
      · rw [g1]; simp [hσ2, hσ1]

end Gen

/-! ## The layout and the program -/

/-- The sixteen unary streams, in `hashNums` order. -/
def hL : List (Fin 17) := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

theorem hL_nodup : hL.Nodup := by decide
theorem hL_ne : ∀ S ∈ hL, S ≠ (0 : Fin 17) := by decide
theorem hL_length : hL.length = 16 := rfl

/-- The writer's OP counter: the data stage's register `rN` (`7`). -/
def qOP : Fin 16 := 7

/-- **The hash numbers' writer**: the leading `0`, then the sixteen unary streams. -/
def qhW : WM 16 16 := .seq (.wr 0 false) (.seq (.fwd 0) (emitsW 0 qOP hL))

def qhCost (cs : List ℕ) : ℕ := 1 + 1 + (1 + 1 + emitsCost cs)

theorem qh_spec (cap : ℕ) (cs : List ℕ) (hcs : cs.length = 16) (σ : WState 16 16)
    (hv : ∀ i (h : i < 16), σ.st ⟨i + 1, by omega⟩ = List.replicate (cs.get ⟨i, by omega⟩) true ∧
      σ.sh ⟨i + 1, by omega⟩ = 0)
    (hO : σ.st 0 = []) (hOh : σ.sh 0 = 0) (hOP : σ.val qOP = 0) (hcap : 2 * (unaryList cs).length ≤ cap) :
    ∃ τ : WState 16 16, WExec cap qhW σ τ (qhCost cs) ∧ τ.st 0 = false :: marks (unaryList cs) ∧
      τ.sh 0 = (τ.st 0).length ∧ (∀ s, s ≠ 0 → τ.st s = σ.st s) ∧ (∀ r, r ≠ qOP → τ.val r = σ.val r) ∧
      τ.cell = σ.cell := by
  have w1 := WExec.wr (cap := cap) (0 : Fin 17) false σ
  set σ1 := σ.sets 0 (writeTapeBit (σ.st 0) (σ.sh 0) false) with hσ1
  have f1 := WExec.fwd (cap := cap) (0 : Fin 17) σ1
  set σ2 := σ1.seth 0 (σ1.sh 0 + 1) with hσ2
  have o2 : σ2.st 0 = [false] := by simp [hσ2, hσ1, hO, hOh, writeTapeBit]
  have st2 : ∀ s, s ≠ 0 → σ2.st s = σ.st s := fun s hs => by simp [hσ2, hσ1, Function.update_apply, hs]
  have sh2 : ∀ s, s ≠ 0 → σ2.sh s = σ.sh s := fun s hs => by simp [hσ2, hσ1, Function.update_apply, hs]
  obtain ⟨τ, q, a1, b1, c1, d1, f1', g1⟩ := emits_spec cap (0 : Fin 17) qOP hL cs σ2 (by rw [hL_length, hcs]) hL_ne
    hL_nodup
    (fun i h hc => by
      have hi : i < 16 := by rw [hL_length] at h; exact h
      have e : hL.get ⟨i, h⟩ = ⟨i + 1, by omega⟩ := by
        interval_cases i <;> rfl
      rw [e, st2 _ (by intro e'; have := congrArg Fin.val e'; simp at this), sh2 _ (by intro e'; have := congrArg Fin.val e'; simp at this)]
      exact hv i hi)
    (by rw [o2]; simp [hσ2, hσ1, hOh])
    (by simp [hσ2, hσ1, hOP]; omega)
  refine ⟨τ, WExec.cast cap (WExec.seq w1 (WExec.seq f1 q)) rfl (by unfold qhCost; omega), ?_, b1, ?_, ?_, ?_⟩
  · rw [a1, o2]; rfl
  · intro s hs; rw [d1 s hs, st2 s hs]
  · intro r hr; rw [f1' r hr]; simp [hσ2, hσ1]
  · rw [g1]; simp [hσ2, hσ1]

end NearCubicWires.WireExponent3_5.PrimT.TS4
