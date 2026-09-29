import Proof.Circuits.BoundedOracleStructuralCircuit
import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.GeneratedBalancedRangeProgram
import Proof.MachineModel.ProjectionRunnerAtomProgram

/-!
# Canonical balanced projection-runner pipeline

The projection verifier has one public row-major schedule.  This module
identifies that typed schedule with the atoms reconstructed by the fixed range
callee, then composes the two canonical balanced calls.  No host-built call
list, linked spine, or compatibility codec exists at the executable boundary.
-/

namespace NearCubicWires.ProjectionRunnerBalancedProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerAtomProgram
open NearCubicWires.ProjectionRunnerCallProgram
open NearCubicWires.VerifiedLinker

/-! ## Public range to typed call atoms -/

/-! ## Canonical atom-construction balanced call -/

/-! ## Canonical imported-runner balanced call -/

/-! ## End-to-end public projection table -/

end NearCubicWires.ProjectionRunnerBalancedProgram
