import Proof.MachineModel.ProjectionRunnerCallProgram

/-!
# Canonical projection-runner atom construction

The public range generator enumerates one flat coordinate.  This fixed,
oracle-free callee turns that coordinate and the public projection shape into
the exact query/decision atom consumed by `projectionRunnerCallProgram`.
Neither a host-generated call list nor a semantic callback crosses this ABI.
-/

namespace NearCubicWires.ProjectionRunnerAtomProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ProjectionRunnerCallProgram

end NearCubicWires.ProjectionRunnerAtomProgram
