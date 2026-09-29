import Proof.CaseAnalysis.RowsModeLiteralPair

/-! The actual complete hash prefix is prepared for the literal-cache cell
scan. Original seed/label/depth fields are retained; all scan heads return. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashReady
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
open CloseoutRowsModeHashLoop CloseoutRowsModeHashSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine CloseoutRowsModeHashSource.machine (fun _=>true)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashReady
