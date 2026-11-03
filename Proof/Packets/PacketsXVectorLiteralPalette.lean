import Mathlib.Tactic
import Proof.Assembly.FixedCore
import Proof.CaseAnalysis.RowsEstimatorSubstitutionMonomial
import Proof.CaseAnalysis.RowsEstimatorSubstitutionOuterRun
import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.CaseAnalysis.RowsModeCacheHash
import Proof.CaseAnalysis.RowsModeCacheSource
import Proof.CaseAnalysis.RowsModeElementary
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.Packets.CycleCommonReserve
import Proof.Packets.DenseAtomMaterialize
import Proof.Packets.NativeNormalized
import Proof.Packets.NormalizedAdditionData
import Proof.Packets.NormalizedMultiplyData
import Proof.Packets.NormalizerCold
import Proof.Packets.PacketsXCycleDenseAtomCost
import Proof.Packets.PacketsXCycleSerializedCost
import Proof.Packets.PacketsXDeltaMetadata
import Proof.Packets.PacketsXLiteralAlphabet
import Proof.Packets.PacketsXLiteralCache
import Proof.Packets.PacketsXLiteralCacheReuse
import Proof.Packets.PacketsXModeCacheBounded
import Proof.Packets.PacketsXNormalizedFiniteTransport
import Proof.Packets.PacketsXNormalizedRing
import Proof.Packets.PacketsXNormalizerOperations
import Proof.Packets.PacketsXReusableArithmeticNat
import Proof.Packets.PacketsXSubstitutionCensus
import Proof.Packets.PacketsXSubstitutionNatInvariant
import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.PacketsXVectorControllerInitialize
import Proof.Packets.PacketsXVectorWorkerChildLoop
import Proof.Packets.PacketsXVectorWorkerDeltaRound
import Proof.Packets.PacketsXVectorWorkerLevelBody
import Proof.Packets.PacketsXVectorWorkerLevelBounded
import Proof.Packets.PacketsXVectorWorkerParentLoop
import Proof.Packets.PacketsXVectorWorkerPrepareRight
import Proof.Packets.PacketsXWindowLevelAtoms
import Proof.Packets.PacketsXWindowLevelProvider
import Proof.Packets.PacketsXWindowLiteralConsume
import Proof.Packets.PacketsXWindowLiteralProvider
import Proof.Packets.PacketsXWindowPositionalSupport
import Proof.Packets.PacketsXWindowRawMeaning
import Proof.Packets.ReusableArithmeticLeft
import Proof.Packets.ReusableNormalizedArithmetic
import Proof.Packets.SubstitutionOuterLoop
import Proof.Packets.VectorAccumulatorRight
import Proof.Packets.VectorChildTransaction
import Proof.Packets.VectorControllerLayout
import Proof.Packets.VectorTerminalBank
import Proof.Packets.WindowSeed
import Proof.Packets.WindowSourceClose
import Proof.Rows.PhysicalFocusBoundary
import Proof.Supplier.EquationZeroField
import Proof.Supplier.RowThresholdSelections
import Proof.Supplier.SupplierCapacity
import Proof.Supplier.SupplierEstimator
import Proof.MachineModel.NativeFanoutReusable

/-! Fifteen source words suffice for the entire cold vector arena. The
fanout's finite routing is independent of all numerical parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding CloseoutRowsModeCache
open NearCubicWires.RepairSource.ProjectionNormalization
noncomputable section

def coldFieldSelect (j : Fin 222) : Option (Fin 15) :=
  if j=117 then some 4 else if j=119 then some 5 else
  if j=120 then some 6 else if j=121 then some 7 else
  if j=122 then some 8 else if j=123 then some 9 else
  if j=124 then some 10 else if j=126 then some 11 else
  if j=143 then some 12 else if j=149 then some 13 else
  if j=150 then some 14 else none

def coldEngineSelect (j : Fin 34) : Option (Fin 15) :=
  if j=13 then some 0 else if j=24 then some 1 else
  if j=31 then some 2 else if j=32 then some 3 else none

def coldSelect : Fin 299 → Option (Fin 15) :=
  Fin.addCases (m:=298) (n:=1) (motive:=fun _=>Option (Fin 15))
    (Fin.addCases (m:=296) (n:=2) (motive:=fun _=>Option (Fin 15))
      (Fin.addCases (m:=264) (n:=32) (motive:=fun _=>Option (Fin 15))
        (Fin.addCases (m:=256) (n:=8) (motive:=fun _=>Option (Fin 15))
          (Fin.addCases (m:=34) (n:=222) (motive:=fun _=>Option (Fin 15))
            coldEngineSelect coldFieldSelect) (fun _=>none)) (fun _=>none)) (fun _=>none)) (fun _=>none)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
