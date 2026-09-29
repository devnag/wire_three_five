import Proof.Hierarchy.CompetitorRawRecordEmit

/-! Two actual normalizers widen the produced positive and negative
numerators for the scalar-stream consumer. Their paid zero counter is
retained for subsequent framed appending. -/
namespace NearCubicWires.RepairOrdinary.CompetitorNumeratorWiden
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 2) : Fin 5 → Fin 9 := if j.val=0 then ![0,1,3,4,5] else ![0,2,6,7,8]
noncomputable def partProgram (j : Fin 2) := RecoveryFocus.machine (slots j) ClockNormalize.machine
noncomputable def machine := Composition.machine (partProgram 0) (partProgram 1)

end NearCubicWires.RepairOrdinary.CompetitorNumeratorWiden
