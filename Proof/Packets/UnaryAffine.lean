import Proof.MachineModel.Runs
import Proof.PCP.ProjectionDimensionTemplate

/-! A fixed finite program computes c*n+d from one raw unary n. Both constants
are printed by finite control, all intermediate words are physically produced,
and every head returns to zero. Pool seed uses (8,12), (1,1), and (2,0). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Completion.UnaryAffine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization




end Completion.UnaryAffine
