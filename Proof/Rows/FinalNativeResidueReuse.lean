import Proof.Rows.FinalNativeResidueRestore

/-! One actual append runs on one persistent bank, pays its head reset,
clears every private tape, and restores the next field reader's canonical
input. Physical template construction and the enclosing stream loop are
separate consumers. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueReuse
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend (F w p : ℕ) (A : Fin 23 → List Bool) : Fin 27 → List Bool :=
  Fin.addCases (m:=23) (n:=4) (motive:=fun _=>List Bool) A (C10NativeResidueRestore.retained F w p)

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueReuse
