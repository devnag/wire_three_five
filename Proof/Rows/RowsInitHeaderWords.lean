import Proof.Amplification.RecoveryScratchErase
import Proof.CaseAnalysis.RowsEstimatorScanRun
import Proof.Hierarchy.CompetitorRecordRewind
import Proof.MachineModel.BlockUnaryCalc
import Proof.PCP.PCPPQueryField
import Proof.PCP.ProjectionRawFrame
import Proof.Rows.CapReader
import Proof.Rows.Plan
import Proof.Assembly.ClosureBinaryCacheMeasure
import Proof.Rows.HeaderErase

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace RowsInit
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.P1Closure
noncomputable section

/-! ## 1. A one-step head bump -/

/-! ## 2. The 29-port Header-word chain -/

/-- Local entry bank: pool word (0), arity template (1), metadata word (2), all else blank. -/
def hdrIn {k : Nat} (gs : List (ExactThresholdGate k)) (m : List Bool) : Fin 29 → List Bool :=
  fun i=>if i=0 then exactListWord gs else if i=1 then UnaryTemplate.tape k else if i=2 then m else []





/-! ## 3. Cost: dominated by the Header's own budget -/

/-! ## 4. The 430 mutable Header reserves `pad U []` -/

/-! ## 5. The consumer's words at the I2a ports -/

end
end RowsInit
