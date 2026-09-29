import Proof.CaseAnalysis.RowsSupportTermAll

/-! The actual canonical term count drives the complete term controller.
The accumulator state below is only proof bookkeeping extracted from its
same receipt; no second interpreter or coefficient pass is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.TermLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open CloseoutWitness
open CloseoutWitness.TermLoop (emitted coefficientWord mass position emitted_succ position_succ mass_succ mass_valid)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section


def machine {s : ℕ} (circuit : Machine 1704 s) :=
  RepeatMachine.machine (Term.machine circuit) (fun _ bits=>bits 724)

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.TermLoop
