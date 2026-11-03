import Proof.Packets.SrcYSite0
import Proof.SourceAssembly.SourceSkelCaps
import Proof.SourceAssembly.SourceSkelFillV5

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
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
namespace NearCubicWires.SourceSkeleton.Final
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section resid
variable {selector : CyclicChoice.Laws} (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) {gamma : Real} (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (k r scratch : Nat)

set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity
set_option hygiene false in
local notation "𝔏" => ParamsV4.LW selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔮" => C10PartsSchedule.widthAt sources k n

def capsSite (n : Nat) : RowCaps :=
  SourceSkeleton.capsU (SourceBudget.Pow2.hFOf2 selector sources p 𝔏 𝔮) (SourceBudget.Pow2.cCOf2 selector sources p 𝔏 𝔮)
    (SourceBudget.Params.VvOf selector sources p 𝔏 𝔮) (SourceBudget.Pow2.rROf2 selector sources p packets 𝔮)

end resid

end
end NearCubicWires.SourceSkeleton.Final
end

