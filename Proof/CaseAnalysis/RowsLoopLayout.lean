import Proof.CaseAnalysis.RowsCutMeaning
import Proof.CaseAnalysis.RowsDegreeClean
import Proof.CaseAnalysis.RowsDegreeNext
import Proof.CaseAnalysis.RowsMetadataReload

/-! One exact boundary for the degree loop: native row context, 57 work
tapes, the retained C driver/logs, and six short templates. The worker
receipt describes every physical head and tape needed by its next call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsLoopLayout
open LocalBitMultitape RecoveryExecution CloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutRowsLoopLayout
