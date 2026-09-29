import Proof.CaseAnalysis.RowsModeLiteralPrefix
import Proof.CaseAnalysis.RowsRawAtomSeek

/-! One actual literal-cache pair. Both scalar flags are physically read;
the original unary index advances even for an empty variable polynomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralPair
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsModeLiteralMarks
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def a:=Composition.machine CloseoutRowsModeLiteralPrefix.machine (emit false)
noncomputable def b:=Composition.machine a (mark true)
noncomputable def c:=Composition.machine b (TapeEmbedding.machine 1 RowMaskBody.machine)
noncomputable def d:=Composition.machine c (mark false)
noncomputable def machine:=Composition.machine d (emit false)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralPair
