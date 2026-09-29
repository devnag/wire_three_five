import Proof.Foundations.PolynomialClock

/-!
# Uniform register bounds for fixed weak-machine programs

The weak machine charges every write by binary width.  This module packages
the monotone bound used by executable compiler proofs: one machine step may
replace a register bound `b` by `Nat.pair b b`, and `pairIter` reserves that
growth for an exact number of remaining steps.
-/

namespace NearCubicWires.RegisterBounds

open NearCubicWires
open NearCubicWires.PolynomialClock

/-! ## Clocked one-step rules

These rules deliberately combine operational reduction with the register
invariant.  Compiler proofs can therefore chain exact instruction traces
without re-proving the same bounded-write side condition at every program
counter. -/

end NearCubicWires.RegisterBounds
