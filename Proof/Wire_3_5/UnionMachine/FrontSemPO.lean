import Proof.Wire_3_5.UnionMachine.C1Ref
import Proof.Wire_3_5.UnionMachine.FrontFmtSem

/-! # C6 front, the semantic core (1): the PCPP output word's layout (P3:3672)

Base's `pcppOutput r p` is `natListWord [sys, aux, cb] ++ bits ++ natListWord lits`: the systematic supports' bitmaps
(`sys` rows of the request's arity) and the clauses' literal indices. **`pcppOutput_poWord`** writes it as C1's
`poWord`; **`sbOf_length`**, **`chunk_sbOf`** (each row is the support's bitmap); at a guess, **`litsOf_eq`** (the literal
list is C1's `litsG`) and **`bm_rows`** (the bitmaps' writer reads the fold's bitmaps).

Paper quantity of the main types: the PCPP output of the guessed oracle's substituted circuit. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPO
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.SourceInterfaces NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (bitmap)

section Word
variable {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)

/-- The systematic supports' bitmaps. -/
def sbOf : List Bool :=
  (List.ofFn (fun i : Fin p.systematicBits => List.ofFn (fun j : Fin r.arity => decide (j ∈ p.systematicSupport i)))).flatten

/-- The clauses' literal indices. -/
def litsOf : List ℕ :=
  (List.ofFn fun i : Fin (2 ^ p.clauseBits) => [literalIndex (p.clauses i).left, literalIndex (p.clauses i).right]).flatten

/-- **The PCPP output word as C1's `poWord`.** -/
theorem pcppOutput_poWord :
    pcppOutput r p = C1Cnt.poWord p.systematicBits p.auxiliaryBits p.clauseBits (sbOf r p) (litsOf r p) := by
  unfold pcppOutput C1Cnt.poWord sbOf litsOf natListWord
  simp [List.append_assoc]

theorem sbOf_length : (sbOf r p).length = p.systematicBits * r.arity := by
  unfold sbOf
  rw [List.length_flatten]
  simp [List.sum_ofFn, Function.comp_def, Finset.sum_const, Finset.card_fin, Nat.mul_comm]

end Word

/-- A row of a flattened family of equal-length rows. -/
theorem chunk_flatten_ofFn {q : ℕ} : ∀ {n : ℕ} (f : Fin n → List Bool) (_hf : ∀ i, (f i).length = q) (i : ℕ)
    (hi : i < n), FrontFmtBM.chunk q (List.ofFn f).flatten i = f ⟨i, hi⟩
  | 0, _, _, _, hi => absurd hi (by omega)
  | n + 1, f, hf, i, hi => by
    rw [List.ofFn_succ, List.flatten_cons]
    cases i with
    | zero =>
      unfold FrontFmtBM.chunk
      simp only [Nat.zero_mul, List.drop_zero]
      rw [List.take_append_of_le_length (by rw [hf 0]), List.take_of_length_le (by rw [hf 0])]
      rfl
    | succ i =>
      have ih := chunk_flatten_ofFn (fun j : Fin n => f j.succ) (fun j => hf j.succ) i (by omega)
      unfold FrontFmtBM.chunk at ih ⊢
      rw [show (i + 1) * q = (f 0).length + i * q by rw [hf 0]; ring, ← List.drop_drop, List.drop_left, ih]
      rfl

section Rows
variable {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)

/-- **Each bitmap row is the support's bitmap.** -/
theorem chunk_sbOf (i : ℕ) (hi : i < p.systematicBits) :
    FrontFmtBM.chunk r.arity (sbOf r p) i = bitmap (p.systematicSupport ⟨i, hi⟩) := by
  unfold sbOf
  rw [chunk_flatten_ofFn _ (fun _ => by simp) i hi]
  rfl

end Rows

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

/-- **The literal list at a guess is C1's `litsG`.** -/
theorem litsOf_eq : litsOf (S.request z g.oracle) g.pcpp = C1Ref.litsG g := by
  unfold litsOf C1Ref.litsG FrontTW.pairsOf
  rw [List.ofFn_eq_map, List.flatMap]

/-- **The bitmaps at a guess**: the bitmap writer's rows are the fold's bitmaps. -/
theorem bm_rows :
    (FrontFmtBM.rows g.q (sbOf (S.request z g.oracle) g.pcpp) g.pcpp.systematicBits ++
      List.replicate g.pcpp.auxiliaryBits (List.replicate g.q false)).flatMap frame =
      (FrontFoldSem.foldOf (g.checkData g.translation)).ys.flatMap frame :=
  FrontFmtSem.bm_eq (D := g.checkData g.translation) _ (fun i hi => chunk_sbOf _ _ i hi)

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPO
