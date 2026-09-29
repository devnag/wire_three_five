import Proof.PCP.BoundedOracleStructuralProjectionTable

/-!
# Table-driven bounded-oracle structural compiler

This is the data boundary used by the executable atom indexer.  The compiler
below consumes only the public shape `(width, queryCount)`, a decoded projection
table, and the circuit bound.  It deliberately reuses the canonical
`BooleanDAGBuilder` operations; there is no second gate representation or
alternate Tseitin schedule.

Correctness proofs and semantic functions stored in `BuiltWire` are erased from
the runtime ABI.  The structural result still contains the exact append-only
builder, extension, and output wire needed to identify the canonical formula.
-/

namespace NearCubicWires.BoundedOracleStructuralTableCompiler

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces

end NearCubicWires.BoundedOracleStructuralTableCompiler
