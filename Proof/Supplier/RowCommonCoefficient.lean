import Proof.Supplier.RowFieldPaddingAppend

/-! The native occurrence coefficient is normalized once, widened directly
to the common cut width, and physically appended. No canonical-radix
coefficient equality or implicit change of the emitted width is used. -/
namespace NearCubicWires.RepairOrdinary.RowCommonCoefficient
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldSlots : Fin 5→Fin 32 := ![26,28,29,30,31]
noncomputable def first := TapeEmbedding.machine 4 RowCoefficientWhole.machine
noncomputable def last := RecoveryFocus.machine fieldSlots RowFieldPaddingAppend.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowCommonCoefficient
