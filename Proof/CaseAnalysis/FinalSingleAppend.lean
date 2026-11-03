import Proof.CaseAnalysis.FinalAppendPositioning

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SingleAppend

open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open CloseoutRowsEstimatorCoefficients

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def raw := Composition.machine
  (Composition.machine CloseoutFinalC10AppendPositioning.enter CloseoutFinalC10AppendPositioning.seek)
  (TapeEmbedding.machine 1 CloseoutFinalC10SiteRoundPortAppend.machine)

noncomputable def machine := MaskedReset.machine raw (fun _ => true)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10SingleAppend
