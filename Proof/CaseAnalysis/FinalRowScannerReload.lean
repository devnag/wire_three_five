import Proof.CaseAnalysis.RowsEstimatorMetadataBatch
import Proof.MachineModel.Layout

/-! Paid scanner restart from a retained padded header and the row's three
produced scalar fields. The D backing and source fields are physical inputs;
this segment allocates neither. Its literal output is the existing Prepare
consumer's padded bank, with all source fields and reset tapes retained. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10RowScannerReload
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.CloseoutRowsEstimator ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 8 → Fin 69 := ![64,65,66,0,17,54,67,68]
noncomputable def first := RecoveryFocus.machine copySlots (MetadataBatch.machine 3)
noncomputable def last := TapeEmbedding.machine 5 Prepare.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairSource.CloseoutFinal.C10RowScannerReload
