import Mathlib.Data.Nat.Choose.Bounds
import Proof.CaseAnalysis.RowsCircuitBottomReturned

/-! A Pascal cell uses the existing streaming binary adder. Its two
actual row cursors consume adjacent fixed-width fields; the sum appends
at the table cursor, and one paid move passes both input delimiters. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalCell
open LocalBitMultitape SignedSortKey RecoveryRootRound
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalCell
