import Proof.Circuits.BoundedOracleStructuralTableCompiler
import Proof.Circuits.CircuitInputClauseBalancedCall

/-!
# Pointwise structural formula from public projection outputs

This is the sole semantic target of the fixed atom callee.  It interprets one
global formula index from the actual projection-runner table and the public
shape; it never accepts a circuit, node schedule, or formula list as context.
-/

namespace NearCubicWires.BoundedOracleStructuralFormulaTable

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralTableCompiler
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces

end NearCubicWires.BoundedOracleStructuralFormulaTable
