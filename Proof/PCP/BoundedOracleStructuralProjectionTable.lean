import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.MachineModel.ProjectionRunnerBalancedProgram

/-!
# Public projection-table semantics for the bounded-oracle compiler

The executable projection runner returns one balanced table: query-coordinate
outputs in row-major order, followed by one decision output for every random
string.  This module gives that table its sole structural interpretation.  In
particular, the compiler-facing functions below decode the actual runner
outputs; they do not invoke either imported runner a second time.
-/

namespace NearCubicWires.BoundedOracleStructuralProjectionTable

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.ProjectionRunnerCallProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## Fixed access to the balanced public table -/

end NearCubicWires.BoundedOracleStructuralProjectionTable
