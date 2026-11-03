import Proof.CaseAnalysis.RowsOriginalWriter

/-! A complete fixed template is written into the ordinary factor-loop
input buffer, then its append cursor returns with a paid log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalWriter
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def readyMachine (factors : List (Fin 2)):=MaskedReset.machine (machine factors) (fun i=>decide (i=2))

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalWriter
