import Proof.MachineModel.CanonicalRowCountExponentProgram
import Proof.MachineModel.RuntimeScheduleNumeralBank

namespace NearCubicWires.RuntimeScheduleQuadNumeralProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The straight-line frames

Each is a fixed instruction list with its own exact width, clock and
execution theorem.  Every width obligation below is `Nat.left_le_pair` or
`Nat.right_le_pair` against the frame's own input or output word. -/

/-! ## 2. The clause-address envelope from the width register -/

/-! ## 3. The outer native width from the published shape runner -/

/-! ## 4. The quad word -/

/-! ## 5. The published identifications

Each numeral the stream emits is *definitionally* the published envelope at the
scheduled length; the seed arity is the one identity that needs a rewrite. -/

end NearCubicWires.RuntimeScheduleQuadNumeralProgram
