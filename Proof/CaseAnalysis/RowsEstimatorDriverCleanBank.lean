import Proof.CaseAnalysis.RowsEstimatorDriverClean

/-! Copy the actual D word, then clear its bounded private producer bank.
Ports 0/1/2/3 are D, an empty zero summand, the new D copy, and its log;
the private producer words follow. Every operation is an original machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverCleanBank
open LocalBitMultitape RecoveryRootRound StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (t : ℕ) (i : Fin (t+1+2)) : Fin (4+t) :=
  if hi : i.val<t then ⟨4+i.val,by omega⟩
  else ⟨if i.val=t then 0 else if i.val=t+1 then 2 else 3,by split_ifs <;> omega⟩

def first (t : ℕ) := TapeEmbedding.machine t ClockUnarySum.machine
noncomputable def last (t K : ℕ) := RecoveryFocus.machine (slots t) (DriverClean.machine t K)
noncomputable def machine (t K : ℕ) := Composition.machine (first t) (last t K)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverCleanBank
