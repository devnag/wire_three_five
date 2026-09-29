import Proof.MachineModel.TotalSelectiveVerifierRowsProgram

/-!
# The fixed-count sub-compiler's run

`totalSelectiveFixedCountProgram` is the `2944`-instruction stream the outermost
controller calls once per candidate node count.  It is a straight-line
controller of `69` instructions with three relocated callees: the
`1095`-instruction fixed-count grammar compiler, the `1791`-instruction
verifier-row scheduler, and the `18`-instruction append transition.

This module executes that controller, discharging
`SelectiveFixedCountProgramRunner` from two named level
premises one level further down.
-/

namespace NearCubicWires.TotalSelectiveFixedCountProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

open NearCubicWires.TotalSelectiveClausesGuardedProgram
open NearCubicWires.TotalSelectiveVerifierRowsProgram

/-! ## 1. Decoding the fixed 2944-instruction stream -/

/-! ## 2. The controller's three stages, at the typed level -/

/-! ## 4. The controller's trace

Every relocated call below goes through the one shared call-frame lemma
`run_selectiveRelocatedCall`; only the straight-line register plumbing between
calls is specific to this level. -/


/-! ## 5. The level runner -/


end NearCubicWires.TotalSelectiveFixedCountProgram
