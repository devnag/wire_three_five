import Batteries.Tactic.OpenPrivate
import Proof.Circuits.StructuralTaggedReverseEntry
import Proof.Supplier.SelectiveClausesGuardRequest

/-!
# One verifier row's run

`selectiveVerifierRowProgram` is the `1657`-instruction stream that compiles one
randomness row of the projection table: a straight-line controller of `56`
instructions with three relocated callees, the `1256`-instruction projected
query compiler, the `10`-instruction tagged lookup and the `335`-instruction
clause-list compiler.

The controller never loops.  It parses its request, asks the query compiler for
the row's whole query list, reads the row's decision code out of the published
table with one tagged lookup, and hands both to the clause compiler; the clause
compiler's wire is the row's wire.

This module executes that controller from two named level premises, the
projected query compiler's run and the clause-list compiler's run.
-/

namespace NearCubicWires.TotalSelectiveVerifierRowProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.BoundedOracleStructuralTableCompiler
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

open NearCubicWires.TotalSelectiveClausesGuardedProgram

/-! ## 1. Decoding the fixed 1657-instruction stream -/

/-! ## 2. The controller's live frame

The whole controller reads one live frame: the compiler state and the nine
request constants.  Every call block rewrites the state registers in place, so
the frame is stated at whichever compiler state is current. -/

/-! ## 3. The three call blocks -/

/-! ## 4. The whole verifier row -/

end NearCubicWires.TotalSelectiveVerifierRowProgram
