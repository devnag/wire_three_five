import Proof.Supplier.RowNativeCoordinate
import Proof.Supplier.RowPowerBlockMeaning

/-! One actual selected weight/target is appended as a signed radix block.
The selected child stays in its original cache; the prefix scanner copies no
field, and the signed appender reuses its separate bounded scratch bank. -/
namespace NearCubicWires.RepairOrdinary.RowNativeCoordinateAppend
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 18 := ![0,16,17,15]
noncomputable def first := RecoveryFocus.machine slots RowNativeCoordinate.machine
noncomputable def last := TapeEmbedding.machine 3 RowPowerNativeReusable.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowNativeCoordinateAppend
