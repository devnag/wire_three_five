import Proof.Supplier.RowCoefficientField

/-! Execute the complete occurrence loop and physically rewind just its two
coefficient heads. The cache, index-stream cursor and loop counter survive;
the paid rewind log supplies real allocated normalization workspace. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientLoopReset
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 25) : Bool := decide (i=10 ∨ i=11)
noncomputable def machine := MaskedReset.machine RowOccurrenceLoop.machine selected

end NearCubicWires.RepairOrdinary.RowCoefficientLoopReset
