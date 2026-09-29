import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.BalancedClauseStreamFlattenProgram
import Proof.MachineModel.CircuitInputClauseProgram
import Proof.MachineModel.CircuitInputTautologyProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.MachineModel.TaggedProgramChoice

/-!
# Canonical balanced batch calls for circuit-input clauses

The recovery controller emits canonical balanced call atoms.  This module
applies the one fixed `CircuitInputClauseProgram` to every atom through the
shared balanced traversal, preserving gate order and returning one balanced
raw-clause stream per gate.
-/

namespace NearCubicWires.CircuitInputClauseBalancedCall

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.CircuitInputCNF
open NearCubicWires.CircuitInputTautologyProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.TseitinCNF
open NearCubicWires.VerifiedLinker

/-! ## One heterogeneous formula-clause callee -/

/-! ## Full circuit-input formula -/

/-! ## Count-preserving handoff -/

/-! ## Full-formula count-preserving handoff -/

end NearCubicWires.CircuitInputClauseBalancedCall
