import Proof.Rows.FinalPrimeRow

/-! # GAP 2: materialising the residue as one framed word on one tape

`RepairCloseoutFinalPrimeRow.residue_loop` leaves the residue of the target
split across two candidate words `T`, `U` and a one-cell flag `F`, selected by
`residueWord`.  Everything downstream (modular multiply-accumulate, the
zero-test of a trial division) wants a single framed word.

This file supplies the missing selection pass and joins it to the loop.

The extra pass is a flat three-tape worker `machine : Machine 3 6` docked into
the *existing* seven-tape bank by `RecoveryFocus`, and joined by
`Composition`, which adds finite control states but no tapes.  So the tape
nesting depth is unchanged: `pass → MaskedReset → RepeatMachine` is still the
whole `Fin.addCases` stack, and every port equality the elaborator would
otherwise have to unfold through that stack is hoisted into the named lemmas
`ambientHeads_port` / `ambientTapes_port` below.

No head reset is needed: the loop body already resets the word heads, so the
selection pass starts with its own ports at zero, and it is the last stage.
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeResidue
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
open RepairSource.VerifierDecoding RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. The selection pass -/



/-! ## 2. Ports into the seven-tape bank, hoisted out of the nesting -/


/-! ## 3. The joined machine -/

def fuel (width Q : ℕ) : ℕ := Q * (FinalPrimeRow.cost width + 3) + 3 + 1 + (2 * width + 2)

/-! ## 4. One prime row, residue delivered as a single framed word -/

end NearCubicWires.RepairOrdinary.FinalPrimeResidue
