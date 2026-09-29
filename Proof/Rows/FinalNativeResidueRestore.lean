import Proof.CaseAnalysis.FinalSelectorLoadMasks
import Proof.CaseAnalysis.RawRowsThresholdAccuracy
import Proof.CaseAnalysis.RowsEstimatorDriverPorts
import Proof.CaseAnalysis.RowsEstimatorParityThreshold
import Proof.Rows.FinalWalkStep

namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueRestore
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true




/-- The next call starts from a physically padded blank driver; its actual
width is produced by the field reader before doubling. -/
def canonical (F w p : ℕ) (source out : List Bool) : Fin 23 → List Bool := fun i=>
  if i=0 then source else if i=22 then out else
  if i=14 ∨ i=15 ∨ i=20 then ZeroPadding.pad F (frame (SignedSortKey.binary w 0)) else
  if i=16 then ZeroPadding.pad F (frame (SignedSortKey.binary w p)) else List.replicate F false

def retained (F w p : ℕ) : Fin 4 → List Bool :=
  ![List.replicate (F+1) false,List.replicate F true,
    frame (SignedSortKey.binary w 0),frame (SignedSortKey.binary w p)]

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueRestore
