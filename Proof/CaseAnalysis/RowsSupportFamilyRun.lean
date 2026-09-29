import Proof.CaseAnalysis.RowsSupportFamilyRound
import Proof.CaseAnalysis.RowsSupportFamilyWork

/-! The original family code is checked once, then its actual count and
field stream drive the complete rejecting sum loop. Failed headers stop
before any sum; successful runs retain the three ordered native streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyRun
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def workerProgram {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ) : Σ z,Machine 3242 z:=
  ⟨_,FamilyWork.machine (FamilyRound.machine circuit k q)⟩
def worker {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ) : Machine 3242 (workerProgram circuit k q).1:=
  (workerProgram circuit k q).2
def program {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ) : Σ z,Machine 3242 z:=
  ⟨_,RecoveryGatedSequence.machine (TapeEmbedding.machine 1 FamilyDock.reader) (worker circuit k q) 724⟩
def machine {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ) : Machine 3242 (program circuit k q).1:=
  (program circuit k q).2



end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyRun
