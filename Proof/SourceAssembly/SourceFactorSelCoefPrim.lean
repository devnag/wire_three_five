import Proof.SourceAssembly.SourceFactorSelCount
import Proof.MachineModel.OrdinaryFrameLoad
import Proof.Amplification.RecoveryProjectionDimensionUnary
import Proof.CaseAnalysis.RowsCountBinary
import Proof.MachineModel.ClockNormalize
import Proof.Hierarchy.CompetitorGcd
import Proof.CaseAnalysis.WitnessGuardedGcd
import Proof.MachineModel.OrdinaryMatrixBucketDivide
import Proof.CaseAnalysis.ScheduleCompare

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.CoefPrim
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
noncomputable section

/-! ## Framed-field loader (source head advances) -/

/-- The cold initializer then the loop, as one machine. -/
def gcdM := Composition.machine CompetitorGcd.cold CompetitorGcd.machine

def gcdCost (w a b : Nat) : Nat := (12 * w + 15) + 1 + (a + b + 1) * (32 * w + 40)

end
end NearCubicWires.SourceFactorSel.CoefPrim

