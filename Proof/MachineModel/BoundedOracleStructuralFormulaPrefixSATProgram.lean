import Proof.MachineModel.CircuitInputFormulaPrefixSATProgram
import Proof.MachineModel.TaggedToBalancedPreservingProgram

/-!
# Bounded-oracle structural formula suffix

This is the sole post-emitter path.  The emitter's exact heterogeneous atom
schedule is consumed by the shared balanced clause fold and raw-clause
prefix-SAT reducer; no circuit code, formula callback, or alternate CNF
builder is introduced here.
-/

namespace NearCubicWires.BoundedOracleStructuralFormulaPrefixSATProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.CircuitInputCNF
open NearCubicWires.CircuitInputFormulaPrefixSATProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TaggedToBalancedPreservingProgram
open NearCubicWires.VerifiedLinker

/-! ## Direct tagged-emitter suffix -/

end NearCubicWires.BoundedOracleStructuralFormulaPrefixSATProgram
