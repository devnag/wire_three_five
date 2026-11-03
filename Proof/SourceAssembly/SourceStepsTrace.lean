import Proof.SourceAssembly.SourceStepsData
import Proof.Packets.BudgetEntryCount

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
open NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section generic
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
    ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
  (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
  (sources : EightSources) (L target : Nat) (mode : Bool)

/-- **The record of call `j`** (`clauseVals`' `⟨coefficient j, total j, denominator j⟩`). -/
abbrev entryAt (j : Nat) : Stream.Entry :=
  ⟨TraceData.coefficientOf coordinate ph ci j, (TraceData.fractionOf coordinate ph ci sources L target mode j).1,
    (TraceData.fractionOf coordinate ph ci sources L target mode j).2⟩

/-- **The emitter payload the chain carries into call `j`**: blank at the first call, then the previous call's payload word. -/
def oldAt (b Dw : Nat) : Nat → List Bool
  | 0 => []
  | j+1 => ZeroPadding.pad Dw (Stream.entryWord b (entryAt coordinate ph ci sources L target mode j))

end generic

section clause
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
variable (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat)
    (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector) (deg : Nat → Nat) (V : Nat)
    (dflt : P1TopDownPaidReusable.Datum) (b : Nat) (H : Nat → Fin (code ph).sourceTapes → Nat) (A : Nat → Fin (code ph).sourceTapes → List Bool)
    (Rc familyCost refillCost firstCost counterReserve : Nat)

set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp
set_option hygiene false in
local notation "vdI" => clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt (InitRun.D0 b) (InitRun.cap0 b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) (oldAt coordC ph ci sources L tgtC modeC b (InitRun.D0 b)) H A Rc familyCost refillCost firstCost counterReserve

end clause

end
end NearCubicWires.SourceSteps
end
