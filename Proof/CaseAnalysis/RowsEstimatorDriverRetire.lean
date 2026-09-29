import Proof.CaseAnalysis.RowsEstimatorDriverCleanBank

/-! Retire both physical D words with the original sweep and halted rewind.
The first D word becomes the rewind log; no third counter is constructed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverRetire
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 1 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def last:=Rewind.machine idle
def machine:=Composition.machine (RecoveryScratchErase.machine 1) last

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverRetire
