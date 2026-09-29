import Proof.CaseAnalysis.WitnessSumWorkRun

/-! A successful sum returns the consumed field cursor, leaves the actual
count sentinel, and clears its one private bank with the same paid H
driver. Failed sums never enter this machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumCleanup
open LocalBitMultitape RecoveryRootRound
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def returned:=Composition.machine SumCursor.rewind (SumCursor.move .left)
noncomputable def machine:=Composition.machine returned SumReset.machine

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumCleanup
