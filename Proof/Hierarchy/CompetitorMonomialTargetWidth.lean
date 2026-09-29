import Proof.Hierarchy.CompetitorDimensions

namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision CompetitorMonomialProducts CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 67) : Fin 75 := i.castAdd 8
def widenSlots : Fin 9 → Fin 75 := ![67,10,24,68,69,70,71,72,73]
noncomputable def productsProgram := RecoveryFocus.machine native CompetitorRationalDecision.productsProgram
noncomputable def widenProgram := RecoveryFocus.machine widenSlots CompetitorNumeratorWiden.machine
noncomputable def prepareProgram := Composition.machine productsProgram widenProgram


end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
