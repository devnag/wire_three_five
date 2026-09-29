import Proof.CaseAnalysis.CloseoutWitnessFamilyColdRun
import Proof.CaseAnalysis.RowsSupportFamilyMode
import Proof.CaseAnalysis.RowsSupportFamilyRun

/-! Actual cold family validation in either mode: paid workspace setup,
canonical exact-V header, every original sum and term, actual circuit
worker, coefficient guard, exact mass test and retained native streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyCold
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth CloseoutWitness
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def body (sym : Bool) (k : ℕ) (q : ℚ):=AppendBank.machine (e:=2) (FamilyRun.machine (FamilyMode.machine sym) k q)
def prepare:=TapeEmbedding.machine 1 FamilyPrepare.machine
def program (sym : Bool) (k : ℕ) (q : ℚ) : Σ s,Machine 3244 s:=
  ⟨_,Composition.machine prepare (body sym k q)⟩
def machine (sym : Bool) (k : ℕ) (q : ℚ) : Machine 3244 (program sym k q).1:=(program sym k q).2

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyCold
