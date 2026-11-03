import Proof.CaseAnalysis.RowsProjectionReset
import Proof.MachineModel.BankMetadata
import Proof.MachineModel.CountIndex
import Proof.CaseAnalysis.RowsMetadataCopy

/-! The same physical last-row index fills both native fields. The paid
shared driver copies it once; all local work extents stay within that driver. -/
namespace NearCubicWires.ExtIncidence.CountIndexCopy
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4→Fin 18:=![11,15,16,17]
noncomputable def count:=TapeEmbedding.machine 3 CountIndex.machine
noncomputable def copy:=RecoveryFocus.machine slots RecoveryBoundedTapeCopy.machine
noncomputable def machine:=Composition.machine count copy

end NearCubicWires.ExtIncidence.CountIndexCopy
