import Proof.SourceAssembly.SourceStepsCallFacts

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section clause
variable (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat)
    (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector) (deg : Nat → Nat) (V : Nat)
    (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat) (old : Nat → List Bool)
    (H : Nat → Fin (code ph).sourceTapes → Nat) (A : Nat → Fin (code ph).sourceTapes → List Bool)
    (Rc familyCost refillCost firstCost counterReserve : Nat)

set_option hygiene false in
local notation "vdH" => clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old H A Rc familyCost refillCost firstCost counterReserve

end clause

end
end NearCubicWires.SourceSteps
end
