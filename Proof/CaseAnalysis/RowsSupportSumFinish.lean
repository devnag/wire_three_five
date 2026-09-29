import Proof.CaseAnalysis.RowsSupportTermMeaning

/-! The existing final mass test acts on the retained term bank. Both
embeddings use the original nested layout, so no tape copy or vector
reassociation is executed. The literal term driver is retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumBody
open LocalBitMultitape CompetitorSumFold RepairSource.VerifierDecoding
open CompetitorValidity (Estimate)
open CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def ending (k : ℕ) (q : ℚ) :=
  TapeEmbedding.machine 1 (TapeEmbedding.machine 1 (TapeEmbedding.machine 1705 (SumFinish.machine k q)))

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumBody
