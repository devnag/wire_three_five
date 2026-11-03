import Proof.Supplier.RowCommonCoordinateBody

/-! All weights and the target are emitted at the one common cut width.
The native arity driver executes the coordinate loop and restores itself. -/
namespace NearCubicWires.RepairOrdinary.RowCommonCoordinateLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine RowCommonCoordinateBody.machine (fun _ _=>true)

end NearCubicWires.RepairOrdinary.RowCommonCoordinateLoop
