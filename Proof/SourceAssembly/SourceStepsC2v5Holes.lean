import Proof.SourceAssembly.SourceStepsC2v5Fill
import Proof.SourceAssembly.SourceFactorSelKeepHole
import Proof.SourceAssembly.SourceFactorSelHappHole

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

section c2holes
open Classical

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
local notation "BTS" => ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)
set_option hygiene false in
local notation "CACHES" => PCJda54a286946142d3_BranchPhases.cache sources p k r (scratchOf mask packets rows sources res) modeC
set_option hygiene false in
local notation "layC" => layF ci
set_option hygiene false in
local notation "K0C" => K0F ci
set_option hygiene false in
local notation "HdZ" => (fun (_ : Nat) (_ : Fin (UOf mask packets rows sources res p k r)) => (0 : Nat))
set_option hygiene false in
local notation "AdZ" => (fun (_ : Nat) (_ : Fin (UOf mask packets rows sources res p k r)) => ([] : List Bool))
set_option hygiene false in
local notation "w0C" => (A ((𝒞).whole (Dims.encT (d := 𝔇) 𝒽 5).castSucc)).take (InitRun.D0 bS)
set_option hygiene false in
local notation "oldC" => fun j => if j = 0 then w0C else oldAt coordC ph ci sources L tgtC modeC bS (InitRun.D0 bS) j
set_option hygiene false in
local notation "vdC" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L layC (degOf sources selector coordC ph ci L tgtC modeC layC) V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) oldC HdZ AdZ Rc familyCost refillCost firstCost counterReserve
set_option hygiene false in
local notation "NC5" => (vdC).entries.length
set_option hygiene false in
local notation "CSPC" => (ChainStartP mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS layC K K0C KH0 V dflt HdZ AdZ familyCost firstCost counterReserve refillCost Rc Rc Rc Rc w0C A H)
set_option hygiene false in
local notation "Inv5C" => (Inv5 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS layC K K0C KH0 V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) HdZ AdZ oldC familyCost firstCost counterReserve refillCost Rc Rc Rc Rc NC5)
set_option hygiene false in
local notation "startC" => (if hst : ∃ H1 A1, CSPC H1 A1 then (Classical.choose hst, Classical.choose (Classical.choose_spec hst)) else ((fun _ => 0 : Fin (UOf mask packets rows sources res p k r + 1) → Nat), (fun _ => [] : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)))
set_option hygiene false in
local notation "H0C" => (fun y : Fin (UOf mask packets rows sources res p k r) => (startC).1 y.castSucc)
set_option hygiene false in
local notation "A0C" => chainView 𝒞 bS vdC NC5 0 (fun y : Fin (UOf mask packets rows sources res p k r) => (startC).2 y.castSucc)
set_option hygiene false in
local notation "seamC" => hSeam ci A (startC).1 (startC).2
set_option hygiene false in
local notation "VVC" => chainVals 𝒞 bS vdC seamC H0C A0C
set_option hygiene false in
local notation "ES" => (⟨𝔇, se.extra, sp.extra, gW, eR, eV, X, (𝒞).sourceTapes + 1, (𝒞).whole, pl, e, Rc, Rk, Ce, Kc, K0e, KH0e, cnt, c15, q284, c17, c18,
  bS, vQ, vMB, vMS, vWS, vRW, vBF, vU0⟩ : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)))
set_option hygiene false in
local notation "NCC" => NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)
set_option hygiene false in
local notation "UU" => UOf mask packets rows sources res p k r

set_option hygiene false in
local notation "CSP5C" => (ChainStartP5 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS layC K K0C KH0 V dflt HdZ AdZ familyCost firstCost counterReserve refillCost Rc Rc Rc Rc w0C A H)
set_option hygiene false in
local notation "Inv6C" => (Inv6 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS layC K K0C KH0 V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) HdZ AdZ oldC familyCost firstCost counterReserve refillCost Rc Rc Rc Rc NC5)
set_option hygiene false in
local notation "start5C" => (if hst : ∃ H1 A1, CSP5C H1 A1 then (Classical.choose hst, Classical.choose (Classical.choose_spec hst)) else ((fun _ => 0 : Fin (UU + 1) → Nat), (fun _ => [] : Fin (UU + 1) → List Bool)))
set_option hygiene false in
local notation "H05" => (fun y : Fin UU => (start5C).1 y.castSucc)
set_option hygiene false in
local notation "A05" => chainView 𝒞 bS vdC NC5 0 (fun y : Fin UU => (start5C).2 y.castSucc)
set_option hygiene false in
local notation "VV5" => chainVals 𝒞 bS vdC (hSeam ci A (start5C).1 (start5C).2) H05 A05

end c2holes

end
end NearCubicWires.SourceSteps
end

