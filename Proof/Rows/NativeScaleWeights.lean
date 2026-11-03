import Proof.Rows.NativeScaleRun
import Proof.CaseAnalysis.RowsOriginalClauseLoop
import Proof.Rows.FinalNativeResidueCallback

/-! The real counted native-field loop consumes the reusable scaled callback.
Every coefficient is read from the native stream and the scaled framed words
are appended in the same order, with no allocation proportional to the prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_NativeScaleWeights
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open SignedSortKey
noncomputable section

def words (a p w : Nat) (zs : List Int) (j : Nat):=
  binary w ((a*FinalPrimeReduce.intResidue p (zs.getD j 0))%p)
def cost (F w U : Nat):=4*F+1024*(w+1)^2+10*U+18*w+53
def budget (N F w U : Nat):=N*(cost F w U+3)+3

end
end PCJ45bee56da9f34d5a_NativeScaleWeights
