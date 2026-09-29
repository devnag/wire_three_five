import Proof.MachineModel.BoundedOracleRecoveryProgram
import Proof.Circuits.CircuitInputClauseBalancedCall

/-!
# Executable circuit-input CNF to prefix-SAT recovery

This module links the sole complete circuit-input clause fold directly to the
raw-clause prefix-SAT suffix.  Its public input is a balanced list of clause
atoms paired with a unary prefix count; no formula code, SAT answer, or host
clause generator crosses the machine boundary.
-/

namespace NearCubicWires.CircuitInputFormulaPrefixSATProgram

open NearCubicWires
open NearCubicWires.BoundedOracleRecoveryProgram
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.CircuitInputCNF
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

end NearCubicWires.CircuitInputFormulaPrefixSATProgram
