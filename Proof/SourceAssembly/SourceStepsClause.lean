import Proof.SourceAssembly.SourceStepsEntryInv4
import Proof.SourceAssembly.SourceStepsNextHole
import Proof.SourceAssembly.SourceStepsNums
import Proof.SourceAssembly.SourceStepsParts1

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
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section clause

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
set_option hygiene false in
local notation "codeF" => fun ph' => skelCodeR mask packets rows sources res hres p k r ph' (refill3 mask packets rows sources res p k r se sp e (g7F ph').2) (preFF ph')
set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity
set_option hygiene false in
local notation "layA" => layoutAtOf sources selector coordC ph ci L tgtC modeC lay
set_option hygiene false in
local notation "factsA" => factsAtOf sources selector compiler coordC ph ci L tgtC modeC
set_option hygiene false in
local notation "vWS" => P1TopDownPaidReusableReserves.workspace (printerOf sources) V
set_option hygiene false in
local notation "vRW" => P1TopDownPaidReusableReserves.rewind (printerOf sources) V
set_option hygiene false in
local notation "vBF" => P1TopDownPaidReusableReserves.buffer V
set_option hygiene false in
local notation "vMB" => InitRun.Mb L vQ
set_option hygiene false in
local notation "vMS" => InitPost.Ms L vQ
set_option hygiene false in
local notation "vU0" => InitRun.U0 L vQ
set_option hygiene false in
local notation "bS" => C10PartsSchedule.entryWidthSchedule sources k r n
set_option hygiene false in
local notation "w0S" => (A ((𝒞).whole (Dims.encT (d := 𝔇) 𝒽 5).castSucc)).take (InitRun.D0 bS)
set_option hygiene false in
local notation "oldS" => fun j => if j = 0 then w0S else oldAt coordC ph ci sources L tgtC modeC bS (InitRun.D0 bS) j
set_option hygiene false in
local notation "vdS" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) oldS Hd Ad Rc familyCost refillCost firstCost counterReserve
set_option hygiene false in
local notation "NS" => (vdS).entries.length
set_option hygiene false in
local notation "Inv5S" => Inv5 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS lay K K0 KH0 V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) Hd Ad oldS familyCost firstCost counterReserve refillCost Rc Rc Rc Rc NS H' A'
set_option hygiene false in
local notation "H0cS" => (fun y : Fin (UOf mask packets rows sources res p k r) => H' y.castSucc)
set_option hygiene false in
local notation "A0cS" => chainView 𝒞 bS vdS NS 0 (fun y : Fin (UOf mask packets rows sources res p k r) => A' y.castSucc)
set_option hygiene false in
local notation "CSP" => ChainStartP mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS lay K K0 KH0 V dflt Hd Ad familyCost firstCost counterReserve refillCost Rc Rc Rc Rc w0S A H H' A'
set_option hygiene false in
local notation "BTS" => ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)
set_option hygiene false in
local notation "OFFS" => PCJda54a286946142d3_BranchPhases.offset sources p k r
set_option hygiene false in
local notation "CACHES" => PCJda54a286946142d3_BranchPhases.cache sources p k r (scratchOf mask packets rows sources res) modeC
set_option hygiene false in
local notation "RF" => refill3 mask packets rows sources res p k r se sp e (g7F ph).2

set_option hygiene false in
local notation "VVS" => chainVals 𝒞 bS vdS seam H0cS A0cS
set_option hygiene false in
local notation "INV" => Nat → (Fin (UOf mask packets rows sources res p k r) → Nat) → (Fin (UOf mask packets rows sources res p k r) → List Bool) → Prop

set_option hygiene false in
local notation "ES" => (⟨𝔇, se.extra, sp.extra, gW, eR, eV, X, (𝒞).sourceTapes + 1, (𝒞).whole, pl, e, Rc, Rk, Ce, Kc, K0e, KH0e, cnt, c15, q284, c17, c18,
  bS, vQ, vMB, vMS, vWS, vRW, vBF, vU0⟩ : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)))

end clause

end
end NearCubicWires.SourceSteps
end

