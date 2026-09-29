import Proof.MachineModel.TotalSelectiveVerifierRowProgram

/-!
# The verifier-row scheduler's run

`totalSelectiveVerifierRowsProgram` is the `1762`-instruction stream that compiles
every verifier row of one candidate node count: a controller of `87`
instructions with two relocated callees, the `1657`-instruction single-row
compiler and the `18`-instruction append transition.

The controller derives two loop constants before it starts — the row count
`2 ^ width` by repeated doubling and the decision-table cursor `count * width`
by repeated addition — then walks the rows in ascending randomness order, one
relocated row compilation per row, with the row cursor and the decision cursor
advancing in lockstep.  Compiled rows stay on one private reverse spine, and the
exit emits the canonical `true` base case and folds that spine back into the
source compiler's right-associated conjunction.

This module executes that controller, discharging
`SelectiveVerifierRowsProgramRunner` from the level premises the
single-row compiler consumes.
-/

namespace NearCubicWires.TotalSelectiveVerifierRowsProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.BoundedOracleStructuralTableCompiler
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

open NearCubicWires.TotalSelectiveClausesGuardedProgram
open NearCubicWires.TotalSelectiveVerifierRowProgram

/-! ## 1. The row schedule, at the typed level -/

/-! ## 2. Decoding the fixed 1762-instruction stream -/

/-! ## 3. The controller's live frame -/

/-! ## 4. The two constant loops

Both run before the row loop and touch only their own two registers, so each is
stated with the generic preservation clause on every other register. -/

/-! ## 5. The row loop -/

/-! ## 6. The reverse `and` fold -/

-- Four steps from the exhausted row loop to the fold's constant base case.

/-! ## 7. The request parser and the level runner -/

end NearCubicWires.TotalSelectiveVerifierRowsProgram
