import Proof.MachineModel.StructuralClauseStreamProgram

/-!
# Fixed circuit-input Tseitin clause emitter

Structural compilers should emit ordinary gate records, not duplicate CNF
templates throughout every loop.  This module is the single executable bridge
from one topological Boolean-DAG node to the exact forward raw triples used by
`StructuralClauseStreamProgram`.

The request contains the already shifted variable of the current gate and a
small structural node tag.  Child gate variables are shifted by the caller;
input-node sources remain free-input variables.  This convention avoids a
second arithmetic path in the emitter while exactly matching
`circuitInputNodeClauses`.
-/

namespace NearCubicWires.CircuitInputClauseProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputCNF
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TseitinCNF

end NearCubicWires.CircuitInputClauseProgram
