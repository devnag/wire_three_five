import Proof.CaseAnalysis.FinalGuardedStageConsumer
import Proof.CaseAnalysis.FinalRetainedPhaseFold
import Proof.CaseAnalysis.RowsOriginalClauseLoop

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ374c44bb8b7f47d9_
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal SourceInterfaces RecoveryRootRound
open CloseoutRowsOriginalSchedule CloseoutFinalC10Realizes
open CloseoutRowsEstimatorCoefficients.Stream
noncomputable section

variable (sources : EightSources) (L B t : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B)
 (body : Fin B → Fin t)

def recordPort (ph : Phase) : Fin t :=
 body (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh (C10TailVerdict.scratchT ph))

def branchFuel (fuel : Phase → Nat) (width : Phase → Nat) :=
 fuel .penalty+1+(fuel .moment+1+(fuel .clause+1+
 C10TailVerdictUniform.tbud (max (width .penalty) (max (width .moment) (width .clause)))))


end
end PCJ374c44bb8b7f47d9_
