import Proof.Amplification.RecoveryViewWidth
import Proof.Rows.FinalNativeResidue
import Proof.Rows.FinalNativeResidueReuse

namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueCallback
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


def coreBudget (negate : Bool) (z : ℤ) (w : ℕ) :=
  C10NativeResidueAppend.budget negate z w+4*natBitLength z.natAbs+11

def bank (F w p : ℕ) (source out : List Bool) :=
  C10NativeResidueReuse.extend F w p (C10NativeResidueRestore.canonical F w p source out)

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueCallback
