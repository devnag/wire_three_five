import Proof.CaseAnalysis.RowsModeIndexBlock
import Proof.PCP.VerifierDecodingField
import Proof.Amplification.RecoveryFocusDock

/-! One real tuple digit is read and emitted as an ordinary index block.
The binary copy is overwritten on each iteration; tuple/width are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleDigit
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first:=TapeEmbedding.machine 3 FieldMachine.machine
def slots : Fin 4→Fin 6:=![1,3,4,5]
noncomputable def last:=RecoveryFocus.machine slots CloseoutRowsModeIndexBlock.machine
noncomputable def machine:=Composition.machine first last

end NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleDigit
