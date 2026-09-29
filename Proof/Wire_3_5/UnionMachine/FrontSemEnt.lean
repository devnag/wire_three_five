import Proof.Wire_3_5.UnionMachine.FrontDecode
import Proof.Wire_3_5.UnionMachine.FrontSemPO

/-! # C6 front, the semantic core (2): the grid entries as the table writer reads them (P3:3672-3674)

The guess's rest holds the codec entries `intWord σ ++ natWord c` (`FrontDecode.encE`); the table writer and the
carrier-code writer read them as `FrontTW.entW (σ < 0, σ ≠ 0, c)` (`gridWord` sign, then the code). On grid signs the
two words agree: **`entsW_esOf`**. The entries by index: **`esOf_getD`**; the atoms' codes: **`codeE_esOf`**.

Paper quantity of the main type: the grid entries (signs and atoms' codes) of the parsed guess. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode

/-- An entry as the table writer reads it: negative sign, nonzero sign, the code. -/
def entOf (e : ℤ × ℕ) : Bool × Bool × ℕ := (decide (e.1 < 0), decide (e.1 ≠ 0), e.2)

theorem entW_entOf (e : ℤ × ℕ) (he : e.1 ∈ gridSet) : FrontTW.entW (entOf e) = encE e := by
  obtain ⟨σ, c⟩ := e
  simp only [gridSet, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;>
    simp [FrontTW.entW, entOf, encE, intWord, FrontEntriesRef.natWord_zero, FrontEntriesRef.natWord_one]

theorem entsW_map (l : List (ℤ × ℕ)) (hl : ∀ e ∈ l, e.1 ∈ gridSet) :
    FrontTW.entsW (l.map entOf) = (l.map encE).flatten := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.map_cons, List.flatten_cons, FrontTW.entsW] at ih ⊢
    rw [entW_entOf e (hl e (by simp)), ih (fun e' h' => hl e' (by simp [h']))]

/-- The linearized family by index. -/
theorem getD_linE {β : Type} (d : β) : ∀ {nv s : ℕ} (f : Fin nv → Fin s → β) (X : Fin nv) (a : Fin s),
    (linE f).getD (X.val * s + a.val) d = f X a
  | 0, _, _, X, _ => X.elim0
  | nv + 1, s, f, X, a => by
    rw [linE_succ]
    refine Fin.cases ?_ (fun X' => ?_) X
    · simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      rw [List.getD_append _ _ _ _ (by simp)]
      simp
    · have ih := getD_linE d (fun X a => f X.succ a) X' a
      rw [show (X'.succ).val * s + a.val = (List.ofFn fun a => f 0 a).length + (X'.val * s + a.val) by
        simp [Fin.val_succ]; ring]
      rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact ih

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

/-- **The guess's entries as the table writer reads them.** -/
def esOf : List (Bool × Bool × ℕ) := (entsG g).map entOf

theorem esOf_length : (esOf g).length = (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * g.s := by
  unfold esOf; rw [List.length_map, entsG_length]

/-- **On grid signs the two entry words agree.** -/
theorem entsW_esOf (hg : ∀ e ∈ entsG g, e.1 ∈ gridSet) : FrontTW.entsW (esOf g) = ((entsG g).map encE).flatten :=
  entsW_map _ hg

/-- **The entries by index.** -/
theorem esOf_getD (X : PcppVar g.pcpp) (a : Fin g.s) :
    (esOf g).getD (X.val * g.s + a.val) (false, false, 0) =
      (decide (g.sign X a < 0), decide (g.sign X a ≠ 0), g.mode.code (g.atom X a)) := by
  unfold esOf entsG
  show (List.map entOf _).getD _ (entOf (0, 0)) = _
  rw [List.getD_map, getD_linE (0, 0) _ X a]
  rfl

/-- **The atoms' codes by index.** -/
theorem codeE_esOf (X : PcppVar g.pcpp) (a : Fin g.s) :
    FrontFmtCA.codeE (esOf g) (X.val * g.s + a.val) = g.mode.code (g.atom X a) := by
  unfold FrontFmtCA.codeE
  rw [esOf_getD]

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt
