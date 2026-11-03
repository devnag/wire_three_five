import Proof.Assembly.Ready
import Proof.Assembly.ClosureBinaryCacheRun
import Proof.Hierarchy.CompetitorRecordRewind

section
/- Source body: PCJ38fbfed565f64139_Cached.lean; unchanged below. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ38fbfed565f64139_Cached
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

structure Program {printer : WilliamsAlgorithm} {work : Nat}
    (row : PCJ38fbfed565f64139_Ready.Program printer work) (U : Nat) where
  familySlots : Fin (PCJ38fbfed565f64139_Ready.tapes printer work+1)→Fin U
  familyInjective : Function.Injective familySlots
  poolSlots : Fin 373→Fin U
  poolInjective : Function.Injective poolSlots
  rewindSlots : Fin 3→Fin U
  rewindInjective : Function.Injective rewindSlots
  directSource : rewindSlots 0=familySlots ((PCJ38fbfed565f64139_Ready.descriptor printer work).castAdd 1)
  seedStates : Nat
  seed : Machine U seedStates
  setupStates : Nat
  setup : Machine U setupStates
  finishStates : Nat
  finish : Machine U finishStates

def before {printer : WilliamsAlgorithm} {work U : Nat}
    {row : PCJ38fbfed565f64139_Ready.Program printer work} (p : Program row U) :=
  Composition.machine p.seed
    (Composition.machine (RecoveryFocus.machine p.poolSlots BinaryCacheColdRun.machine) p.setup)
def after {printer : WilliamsAlgorithm} {work U : Nat}
    {row : PCJ38fbfed565f64139_Ready.Program printer work} (p : Program row U) :=
  Composition.machine (RecoveryFocus.machine p.rewindSlots CompetitorRecordRewind.machine) p.finish

def code {printer : WilliamsAlgorithm} {work U : Nat}
    {row : PCJ38fbfed565f64139_Ready.Program printer work} (p : Program row U) :
    PCJ38fbfed565f64139_Cycle.Code (PCJ38fbfed565f64139_Ready.code row) U where
  slots := p.familySlots
  injective := p.familyInjective
  beforeStates := _
  before := before p
  afterStates := _
  after := after p

def cacheArgs {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L) :
    BinaryCacheColdJoin.Args q :=
  ⟨Packets.live F,C10SupplierRowInput.childList a (Packets.live F) F.occurrences⟩

def descriptorWord (printer : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum) :=
  ds.flatMap (P1TopDownPaidReusable.Datum.word printer)

end
end PCJ38fbfed565f64139_Cached

end

section
/- Source body: PCJ38fbfed565f64139_Source.lean; unchanged below. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed
namespace PCJ38fbfed565f64139_Physical
attribute [local irreducible] P1TopDownPaidPayload.tapes

end PCJ38fbfed565f64139_Physical

end

section
/- Source body: PCJ38fbfed565f64139_Phase.lean; unchanged below. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open PCJ1fef9807c6954e94_Native

open PCJ9eff70d512234a4c_Fixed
namespace PCJ38fbfed565f64139_Physical

end PCJ38fbfed565f64139_Physical

end

section
/- Source body: PCJ38fbfed565f64139_Selected.lean; unchanged below. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open PCJ1fef9807c6954e94_Native

open PCJ9eff70d512234a4c_Fixed
namespace PCJ38fbfed565f64139_Physical

end PCJ38fbfed565f64139_Physical

end

section
/- Source body: PCJ38fbfed565f64139_Parent.lean; unchanged below. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open PCJ1fef9807c6954e94_Native

open PCJ9eff70d512234a4c_Fixed
namespace PCJ38fbfed565f64139_Physical

end PCJ38fbfed565f64139_Physical

end
