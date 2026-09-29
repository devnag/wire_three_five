import Proof.CaseAnalysis.WitnessTermLoopMeaning

/-! The existing final mass test acts on the retained term bank. Both
embeddings use the original nested layout, so no tape copy or vector
reassociation is executed. The literal term driver is retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumBody
open LocalBitMultitape CompetitorSumFold RepairSource.VerifierDecoding
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutWitness.SumBody
