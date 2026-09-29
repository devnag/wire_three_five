import Proof.Wire_3_5.Primitive.SeedFix.HbWM2
import Proof.Wire_3_5.UnionMachine.RegRatOps

/-! # SEEDFIX C4.L: the recovery of a printed table (`alg:recovery`, P3:1965-1982)

"Reduction must precede the column sum" (P3:1965-1982): the printer leaves, per cell of its table, the least residue of
the printed value modulo `2^{Q'}` as `Q'` binary bits (`CompetitorFinalTable.word`, the cells in row-major order); the
recovered sum is the sum of those residues. The recovery program reads the table's `K` residues `q` bits at a time,
widens each to a framed `W`-bit word (`TMP`) and adds it to the accumulator `ACC` with C6's binary adder
(`RegRat.addB`). **`recW_spec`**: `ACC` ends as `frame (binary W (vs.sum))` for the table `vs.flatMap (binary q)`.

Paper quantity of the main type: the recovered column sum `vs.sum`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Rec
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)


theorem frame_odd' : ∀ (w : List Bool) (i : ℕ), readTapeBit (frame w) (2 * i + 1) = w.getD i false
  | [], i => by simp [frame, readTapeBit]
  | b :: w, 0 => by simp [frame, readTapeBit]
  | b :: w, i + 1 => by
    have := frame_odd' w i
    simp only [readTapeBit] at this ⊢
    rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by ring]
    simpa [frame] using this

section Bits

end Bits

section Chunk

end Chunk

section Zero
variable (cap : ℕ)

theorem frame_rep_false : ∀ n : ℕ, frame (List.replicate n false) = PrimAsm.FiltRec.reps n [true, false] ++ [false]
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ]
    show true :: false :: frame (List.replicate n false) = _
    rw [frame_rep_false n]
    unfold PrimAsm.FiltRec.reps
    rw [List.replicate_succ, List.flatten_cons]
    rfl

end Zero

section Loop

end Loop

end NearCubicWires.WireExponent3_5.PrimT.C4Rec
