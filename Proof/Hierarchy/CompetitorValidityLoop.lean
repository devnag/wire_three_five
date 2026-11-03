import Proof.Hierarchy.CompetitorValidityBody

/-! Whole ordinary validity-record loop. Failed comparisons halt immediately;
successful iterations reuse the same bounded scalar workspace and leave the
global stream cursor at the next record. The physical list driver is reset
on exhaustion, and every entry, return and reset is charged. -/
namespace NearCubicWires.RepairOrdinary.CompetitorValidity
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (scanned : Fin 71 → Bool) := scanned 65
def words (b : ℕ) (xs : List Comparison) := xs.flatMap (fun a => a.word b)

end NearCubicWires.RepairOrdinary.CompetitorValidity
