import Proof.Hierarchy.CompetitorCountProducerTemplate
import Proof.Hierarchy.CompetitorCountRecordPrepare

/-! The prepared exact selected SUM is consumed directly by the record
appender. This caller derives zero and append workspace from its scalar
width; it does not repeat the table scan or SUM. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountRecordAppend
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prepareSlots (i : Fin 23) : Fin 29 := i.castAdd 6
def fields : List (Fin 29) := [23,24,25,20,26,27]
noncomputable def prepare := RecoveryFocus.machine prepareSlots CompetitorCountRecordPrepare.machine
noncomputable def emit := CompetitorRawFieldEmit.listProgram (28 : Fin 29) 22 fields
noncomputable def machine := Composition.machine prepare emit

def budget (b : ℕ) := CompetitorCountRecordPrepare.budget b+1+(40*b+56)

end NearCubicWires.RepairOrdinary.CompetitorCountRecordAppend
