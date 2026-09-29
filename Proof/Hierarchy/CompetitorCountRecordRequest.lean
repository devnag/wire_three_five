import Proof.Hierarchy.CompetitorCountRecordAppendBounds
import Proof.Hierarchy.CompetitorSelectedRequestCountLayout

/-! One fixed program executes the original Request's selected-count SUM
and appends the exact six-field record. The request derives every SUM driver,
scalar width and record workspace; only the actual mask/count table and
coefficient/normalization fields remain row-producer inputs. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountRecordRequest
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
open CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 29 → Fin 118 :=
  ![76,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,86,117]
noncomputable def first := TapeEmbedding.machine 27 CompetitorSelectedRequestCount.machine
noncomputable def last := RecoveryFocus.machine slots CompetitorCountRecordAppend.machine
noncomputable def machine := Composition.machine first last
def budget (r : Request) (Q : ℕ) := CompetitorSelectedRequestCount.budget r Q+1+
  CompetitorCountRecordAppend.budget (scalarWidth r Q)

end NearCubicWires.RepairOrdinary.CompetitorCountRecordRequest
