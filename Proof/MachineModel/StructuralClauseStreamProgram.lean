import Proof.Circuits.CircuitInputCNF

/-!
# Fixed structural-clause stream encoder

Structural circuit compilers naturally emit Tseitin clauses in forward order,
while `DynamicCNFBuilder` consumes canonical clause codes in reverse order.
This module provides the single fixed bridge between those representations.
Its input is only a tagged stream of raw three-literal tuples; the interpreter
constructs every canonical list cell and reverses the stream by accumulation.
-/

namespace NearCubicWires.StructuralClauseStreamProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputCNF
open NearCubicWires.DynamicCNFBuilder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.TseitinCNF

end NearCubicWires.StructuralClauseStreamProgram
