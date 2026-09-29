import Proof.Hierarchy.CompetitorSumCopyback

/-! The native scalar addition is installed on the actual term-stream
layout. Its result fields and bounded support feed the paid copyback parent. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (j : Fin 88) : Fin 94 := j.castAdd 6
noncomputable def nativeProgram := RecoveryFocus.machine nativeSlots CompetitorRationalSum.machine


noncomputable def restoreProgram := Composition.machine (clearProgram accumulatorSlot) copyAllProgram

end NearCubicWires.RepairOrdinary.CompetitorSumFold
