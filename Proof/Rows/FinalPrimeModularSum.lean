import Proof.Rows.FinalPrimeResidueWord

/-! # GAP 3: gated modular addition and modular accumulation

The threshold row of Appendix A.13 is
`(∑ i, weights i * bitInt (input i)) - target  (mod p)`.  Because `bitInt` of a
Boolean is `0` or `1`, the products are *gated* coefficients, not general
multiplications, so the row is a modular accumulation of coefficient residues
under a gate stream.

This file supplies that accumulation.  `machine : Machine 6 34` performs one
whole update

    res := (res + gate * x)  (mod p)

in a single left-to-right sweep of framed `L`-bit words, running the two carry
chains (`res + gate*x`, then `+ (2^L - p)`) simultaneously in its finite
control.  As in `FinalPrimeRow` the two candidates are written in place on `T`
and `U` and the decisive carry on the one-cell tape `F`, so the next sweep
consumes them directly and `FinalPrimeResidue` materialises the answer.

Tapes: `0 = T`, `1 = U`, `2 = P`, `3 = F` (one cell, head pinned at 0),
`4 = G` (the gate stream, one cell per sweep), `5 = X` (the summand stream,
one framed word per sweep).  Only `T`, `U`, `P` are reset between sweeps, so
the nesting is again exactly `pass -> MaskedReset -> RepeatMachine`: three
tape levels, no fourth.

Driving this machine with a gate stream that is constantly `true` and a
summand stream `x, x, ...` interleaved with `FinalPrimeRow.machine` sweeps on
an empty bit tape (which perform `res := 2*res mod p`) is the shift-add-reduce
modular multiplication; that schedule is a driver, not a new machine.
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeModular
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
open RepairSource.VerifierDecoding RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Finite control -/




/-! ## 2. The four local transitions -/

/-! ## 3. One sweep -/

/-! ## 4. The whole pass -/

/-! ## 5. Exact arithmetic of one gated modular addition -/

/-! ## 6. The summand stream and the driven accumulation -/

def cost (width : ℕ) : ℕ := 2 * (2 * width + 2) + 2

def blocks (w : ℕ → List Bool) : ℕ → ℕ → List Bool
  | _, 0 => []
  | j, n + 1 => frame (w j) ++ blocks w (j + 1) n

theorem blocks_length (w : ℕ → List Bool) (width : ℕ) (hw : ∀ i, (w i).length = width) (j n : ℕ) :
    (blocks w j n).length = n * (2 * width + 1) := by
  induction n generalizing j with
  | zero => simp [blocks]
  | succ n ih => simp [blocks, ih (j + 1), hw j]; ring

end NearCubicWires.RepairOrdinary.FinalPrimeModular
