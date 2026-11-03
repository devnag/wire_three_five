import Proof.Supplier.RowCoefficientDock

/-! One fixed ordinary program consumes the retained cache and the actual
ordered occurrence stream, computes one stacked coefficient, physically
rewinds its P/N words, and emits its final normalized signed field. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientWhole
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding RowCoefficientDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 2 RowCoefficientLoopReset.machine
noncomputable def last := RecoveryFocus.machine slots RowCoefficientField.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowCoefficientWhole
