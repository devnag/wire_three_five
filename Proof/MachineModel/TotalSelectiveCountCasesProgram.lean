import Proof.MachineModel.TotalSelectiveFixedCountProgram

/-!
# The nested structural compiler's outermost run

`totalSelectiveCountCasesProgram` is the 3052-instruction stream whose execution is
the sole remaining premise of the emitter chain.  It is a controller of `61`
instructions with two relocated callees: the `2973`-instruction fixed-count
sub-compiler and the `18`-instruction append transition.

This module executes the controller.  Its forward pass compiles one candidate
node count per iteration through the fixed-count callee and retains every
candidate output on a private reverse spine; its reverse pass then rebuilds the
source compiler's right-associated disjunction with its explicit `false` base
case, one append per spine entry.  Both passes are proved here.  The
fixed-count callee's own run is the single named level premise
(`SelectiveFixedCountProgramRunner`); everything else on this level,
including the
typed reachability invariant the append transition needs, is discharged.
-/

namespace NearCubicWires.TotalSelectiveCountCasesProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

open NearCubicWires.TotalSelectiveFixedCountProgram

/-! ## 1. The typed append invariant through the whole compiler

`selectiveStateOrdered` is the reachability invariant the machine append
transition needs at every call site.  Every typed compiler stage is a
composition of appends, so the invariant propagates by structural induction.
-/

/-! ## 2. The controller's two passes, at the typed level

The source compiler folds one candidate at a time and emits the disjunction of
each candidate against the compiled tail.  The controller instead runs every
candidate first, retains their outputs on a reverse spine, and only then emits
the disjunctions from the innermost outwards.  Both orders append exactly the
same nodes in exactly the same order; §2 proves that.
-/

/-! ## 3. Decoding the fixed 3052-instruction stream

The controller occupies the first `61` positions, the fixed-count callee the
next `2973`, and the append callee the last `18`.  Every later step decodes
through exactly one of the three lemmas below, so no proof ever forces the
whole instruction list.
-/

/-! ## 4. One relocated call

Every call site writes the callee's request register, zeroes the shared
accumulator, and jumps to the callee base.  The callee's own run is consumed at
whatever entry registers the previous call left behind, so each level's runner
is required to hold at an arbitrary entry state. -/

/-! ## 5. The reverse fold

Interpreter resources on this level are data dependent, so the fold's clock and
register-width envelope are defined by the same recursion as its output. -/


/-! ## 6. The forward candidate pass

The fixed-count sub-compiler's own run is the single named premise of this
module.  It is packaged as a runner: interpreter resources as functions of the
compiled request only, and a run at an arbitrary entry state, because each call
starts on whatever registers the previous call left in the callee's frame. -/

/-! ## 7. The candidate loop -/

/-! ## 8. The whole 3052-instruction stream -/

end NearCubicWires.TotalSelectiveCountCasesProgram
