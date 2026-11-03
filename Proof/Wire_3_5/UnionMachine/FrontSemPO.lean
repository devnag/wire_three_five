import Lean
import Proof.Wire_3_5.UnionMachine.C1Ref
import Proof.Wire_3_5.UnionMachine.FrontFmtSem
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.FrontSemPOBase


noncomputable section


/-! # C6 front, the semantic core (1): the PCPP output word's layout (P3:3672)

Base's `pcppOutput r p` is `natListWord [sys, aux, cb] ++ bits ++ natListWord lits`: the systematic supports' bitmaps
(`sys` rows of the request's arity) and the clauses' literal indices. **`pcppOutput_poWord`** writes it as C1's
`poWord`; **`sbOf_length`**, **`chunk_sbOf`** (each row is the support's bitmap); at a guess, **`litsOf_eq`** (the literal
list is C1's `litsG`) and **`bm_rows`** (the bitmaps' writer reads the fold's bitmaps).

Paper quantity of the main types: the PCPP output of the outer verifier `H_Γ`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPO
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.SourceInterfaces NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (bitmap)

section Word

end Word

section Rows

end Rows

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

/-- **The literal list at a guess is C1's `litsG`.** -/
theorem litsOf_eq : litsOf (S.request z g.pair) g.pcpp = C1Ref.litsG g := by
  unfold litsOf C1Ref.litsG FrontTW.pairsOf
  rw [List.ofFn_eq_map, List.flatMap]

/-- **The bitmaps at a guess**: the bitmap writer's rows are the fold's bitmaps. -/
theorem bm_rows :
    (FrontFmtBM.rows g.q (sbOf (S.request z g.pair) g.pcpp) g.pcpp.systematicBits ++
      List.replicate g.pcpp.auxiliaryBits (List.replicate g.q false)).flatMap frame =
      (FrontFoldSem.foldOf (g.checkData g.translation)).ys.flatMap frame :=
  FrontFmtSem.bm_eq (D := g.checkData g.translation) _ (fun i hi => chunk_sbOf _ _ i hi)

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPO

end
