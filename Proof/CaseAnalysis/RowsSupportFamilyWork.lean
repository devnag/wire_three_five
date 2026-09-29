import Proof.CaseAnalysis.RowsSupportAppendBank
import Proof.CaseAnalysis.RowsSupportExchange
import Proof.CaseAnalysis.WitnessFamilyWork

/-! The actual extended rejecting family loop shares the original outer
count driver and177-tape header bank. Static labels keep support last. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyWork
open LocalBitMultitape RecoveryRootRound CloseoutWitness
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def renamed {s : ℕ} (body : Machine 3064 s):=
  TapeRenaming.machine (Exchange.layout 3063) (RepeatMachine.machine body (fun _ bits=>bits 724))
def loop {s : ℕ} (body : Machine 3064 s):=AppendBank.machine (e:=177) (renamed body)
def move:=TapeEmbedding.machine 1 CloseoutWitness.FamilyWork.move
def machine {s : ℕ} (body : Machine 3064 s):=Composition.machine move (loop body)

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyWork
