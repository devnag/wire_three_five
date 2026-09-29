import Proof.MachineModel.StructuralClauseStreamProgram

/-!
# Fixed emitter for free-input tautology clauses

`circuitInputFormula` begins with one three-literal tautology for each free
input variable.  This fixed program emits that exact raw clause from only its
variable index, completing the non-gate structural template needed by the
recovery controller.
-/

namespace NearCubicWires.CircuitInputTautologyProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputCNF
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TseitinCNF

end NearCubicWires.CircuitInputTautologyProgram
