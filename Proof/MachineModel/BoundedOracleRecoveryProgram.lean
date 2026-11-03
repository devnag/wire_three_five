import Proof.Amplification.CanonicalRecoveryLanguage
import Proof.Foundations.DynamicCNFBuilder
import Proof.MachineModel.StructuralClauseStreamProgram

/-!
# Executable bounded-oracle recovery

This module owns the public request syntax and the fixed-program boundary for
Appendix C.12 recovery.  Requests contain only the original input, the circuit
bound, and the requested description coordinate.  In particular, no circuit,
CNF, SAT answer, semantic verifier, or recovery callback is accepted as input.

The structural-CNF controller is intentionally assembled from the published
fixed PCP runners and the shared `DynamicCNFBuilder`/zero-first SAT reducer.
Keeping the request codec here makes that trust boundary independently
auditable before the larger linked controller is introduced below.
-/

namespace NearCubicWires.BoundedOracleRecoveryProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CircuitInputCNF
open NearCubicWires.DynamicCNFBuilder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## Fixed request-normalization prefix -/

/-! ## Shared resource widening -/

/-! ## CNF stream to zero-first input -/

/-! ## Forward raw triples to the canonical prefix-SAT input -/

end NearCubicWires.BoundedOracleRecoveryProgram
