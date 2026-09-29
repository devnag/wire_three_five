import Proof.Supplier.RowNativeCoordinateAppend

/-! Original retained native child cache → selected coordinate → one signed
radix block, on a fixed20-tape machine. Cache/arity/selection drivers persist. -/
namespace NearCubicWires.RepairOrdinary.RowCachedCoordinateAppend
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5 → Fin 20 := ![0,16,17,18,19]
noncomputable def first := RecoveryFocus.machine slots DecompositionCachedChild.machine
noncomputable def last := TapeEmbedding.machine 2 RowNativeCoordinateAppend.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowCachedCoordinateAppend
