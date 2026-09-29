import Proof.Wire_3_5.Primitive.SeedFix.S3Circ
import Proof.Wire_3_5.Primitive.SeedFix.S3Ref
import Proof.Wire_3_5.Primitive.SeedFix.S3Wr

/-! # S3, part 7: the evaluator's program layout and one circuit's factor in it (P3:3170-3178)

The per-point evaluator (`Seams.SymPtEval2`) runs on its own layout `WM 27 67`, lifted at the end into the caller's by
the seam's embeddings: streams `0 … 2` the point (`frame (ofFn c)`, `frame (ofFn e_L(u))`, `frame (ofFn e_R(v))`),
`3 … 18` the call words (`symWords`), `19 … 27` scratch; registers `0` the accumulator, `1 … 18` the call numbers
(`symNums`), `19 … 66` scratch (`19 … 50` the circuit program's). Here:

* `flatTable_len` (a flat table's length does not depend on the seed), `tables_read` (the declared all-seeds word
  read at seed `i`), `levelWord_len`;
* `circJ j`: the circuit program (`circS`) lifted onto circuit `j`'s words and the scratch; **`circJ_spec`**: from
  scratch that only READS like the circuit program's entry (C5's specs state exact contents; `ReadEq.wexec_sim`),
  the factor in `qS 28`, the scratch reading like the circuit program's exit, the words and the point kept.

Paper quantity of the main type: one circuit's factor `termOk X W R⁺ R⁻` at the point (a conjunct of `R̂`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Term NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimT.ReadEq

/-! ## Lengths and reads of the declared words -/

theorem frame_len (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  rw [frame_eq_frameP, List.length_append, frameP_length]; rfl

theorem flatTable_len (Pl : FlatListParams) (el : Pl.FlatSeed) (L : ℕ) :
    (flatTable Pl el L).length = Pl.walkLen * (1 + (Pl.base.J + 1) * (2 * L + 1)) + 1 := by
  unfold flatTable
  simp only [List.length_append, List.length_flatMap, List.length_cons, frame_len, rowsOf, List.length_map,
    List.length_range, List.length_singleton, levels, List.length_reverse, List.map_const', List.sum_replicate,
    smul_eq_mul, List.length_finRange]
  simp only [List.length_nil]
  ring

theorem flatMap_getD {α : Type} (f : α → List Bool) (lam : ℕ) : ∀ (xs : List α), (∀ x ∈ xs, (f x).length = lam) →
    ∀ (i p : ℕ) (hi : i < xs.length), p < lam → (xs.flatMap f).getD (i * lam + p) false = (f (xs[i]'hi)).getD p false
  | [], _, i, p, hi, _ => by simp at hi
  | x :: xs, hl, i, p, hi, hp => by
    have hl0 : (f x).length = lam := hl x (by simp)
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by omega)]
      rfl
    | succ i =>
      rw [List.getD_append_right _ _ _ _ (by rw [hl0, Nat.succ_mul]; omega)]
      rw [show (i + 1) * lam + p - (f x).length = i * lam + p by rw [hl0, Nat.succ_mul]; omega]
      rw [flatMap_getD f lam xs (fun x' hx' => hl x' (by simp [hx'])) i p (by simp at hi; omega) hp]
      rfl

theorem tables_read (k : Seams.SymCall) (j : Fin 4) (i : Fin (Fintype.card k.Pl.FlatSeed)) (p : ℕ)
    (hp : p < tabLen k j) :
    readTapeBit (tablesJ k j) (i.val * tabLen k j + p) =
      readTapeBit (flatTable k.Pl (seedOf k i) (gatesJ k j).length) p := by
  unfold readTapeBit tablesJ
  have hlen : ∀ i' ∈ List.finRange (Fintype.card k.Pl.FlatSeed),
      (flatTable k.Pl (seedOf k i') (gatesJ k j).length).length = tabLen k j := by
    intro i' _
    unfold tabLen
    rw [flatTable_len, flatTable_len]
  rw [flatMap_getD (fun i' => flatTable k.Pl (seedOf k i') (gatesJ k j).length) (tabLen k j) _ hlen i.val p
    (by simp) hp]
  simp

/-! ## The layout -/

/-- The evaluator's programs and states. -/
abbrev BM := WM 27 67
abbrev BS := WState 27 67

scoped notation "bC" => (0 : Fin 28)
scoped notation "bU" => (1 : Fin 28)
scoped notation "bV" => (2 : Fin 28)
scoped notation "bPos" => (19 : Fin 28)
scoped notation "bNeg" => (20 : Fin 28)
scoped notation "bX" => (21 : Fin 28)
scoped notation "bZ" => (22 : Fin 28)
scoped notation "bSp" => (23 : Fin 28)
scoped notation "bSm" => (24 : Fin 28)
scoped notation "bT5" => (25 : Fin 28)
scoped notation "bSS" => (26 : Fin 28)
scoped notation "bFT" => (27 : Fin 28)

/-- Word `w`'s stream. -/
def bW (w : Fin 16) : Fin 28 := ⟨3 + w.val, by omega⟩
/-- Number `i`'s register. -/
def qN (i : Fin 18) : Fin 67 := ⟨1 + i.val, by omega⟩
/-- The circuit program's register `q`. -/
def qS (q : Fin 32) : Fin 67 := ⟨19 + q.val, by omega⟩

/-- Circuit `j`'s embedding of the circuit program's streams. -/
def fsJ (j : Fin 4) : Fin 14 → Fin 28 :=
  ![bW (wIdx 0 j), bC, bU, bV, bPos, bNeg, bX, bZ, bSp, bSm, bT5, bSS, bFT, bW (wIdx 1 j)]

theorem fsJ_inj (j : Fin 4) : Function.Injective (fsJ j) := by
  fin_cases j <;> decide

theorem qS_inj : Function.Injective qS := fun a b h => by
  have := congrArg Fin.val h; simp only [qS] at this; exact Fin.ext (by omega)

/-- **Circuit `j`'s factor on the evaluator's layout.** -/
def circJ (j : Fin 4) : BM := circS.liftW (fsJ j) qS

end NearCubicWires.WireExponent3_5.PrimT.S3
