import Proof.SourceAssembly.SourceStepsSite2
import Proof.Packets.SrcStartStatic

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
namespace NearCubicWires.SourceStart.C2RP
open NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section rprows
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
local notation "startC" => (if hst : ∃ H1 A1, SP ci A H H1 A1 then (Classical.choose hst, Classical.choose (Classical.choose_spec hst)) else ((fun _ => 0 : Fin (UOf mask packets rows sources res p k r + 1) → Nat), (fun _ => [] : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)))
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

end rprows

section rpsite
open NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceSkeleton.FirstW NearCubicWires.SourceStart.EntryW
open NearCubicWires.SourceSkeleton.KeptW NearCubicWires.SourceSkeleton.ClassV4 NearCubicWires.SourceSkeleton.ParamsV4

set_option hygiene false in
local notation "CODE" => skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows)
  (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows))
  (ParamsV4.fPW selector xtra mask packets rows)
  (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _
    (FirstW.g7OfW selector xtra G7 mask packets rows)) (FirstW.firstW selector xtra G7 mask packets rows)
set_option hygiene false in
local notation "𝔉" => forcedChoices mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows)
set_option hygiene false in
local notation "denI" => (𝔉).capIndex sources gamma hg hh p + 1
set_option hygiene false in
local notation "kI" => kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "rI" => rSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "resI" => resSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "modeI" => PCJ374c44bb8b7f47d9_.S.mode sources p (denI) (Nat.succ_pos _) kI rI (scrSite selector mask packets rows sources gamma hg hh p) n x bits hp
set_option hygiene false in
local notation "oracleI" => C10TotalDecode.oracleOf sources kI (PolynomialClock.ordinaryClock kI) p.degree n bits
set_option hygiene false in
local notation "coordI" => PCJd04de0277f804fcc_.coordinate sources kI (PolynomialClock.ordinaryClock kI) p (denI) x oracleI bits
set_option hygiene false in
local notation "tgtI" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "LI" => ParamsV4.LW selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "UI" => UOf mask packets rows sources resI p kI rI
set_option hygiene false in
local notation "NCI" => NC sources kI (PolynomialClock.ordinaryClock kI) x oracleI
set_option hygiene false in
local notation "RcI" => Once.Rc (ClassV4.hRx4 selector mask packets rows sources gamma hg hh p) LI 1 (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "VI" => SourceBudget.Params.cVcN selector sources gamma hg hh p *
  RuntimeShape.tableClass LI (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "bI" => C10PartsSchedule.entryWidthSchedule sources kI rI n
set_option hygiene false in
local notation "seI" => (DSite selector mask packets rows sources gamma hg hh p).se
set_option hygiene false in
local notation "spI" => (DSite selector mask packets rows sources gamma hg hh p).sp
set_option hygiene false in
local notation "eI" => eSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "hresI" => resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows) sources gamma hg hh p
set_option hygiene false in
local notation "g7FI" => fun ph' => FirstW.g7OfW selector xtra G7 mask packets rows sources gamma hg hh p modeI ph'
set_option hygiene false in
local notation "preFFI" => fun ph' => FirstW.firstW selector xtra G7 mask packets rows sources gamma hg hh p modeI ph'
set_option hygiene false in
local notation "siteI" => (CODE).site sources gamma hg hh p
set_option hygiene false in
local notation "EtI" => EWFam selector xtra mask packets rows (CODE) sources gamma hg hh p n x bits hp
set_option hygiene false in
local notation "EFI" => EFSite selector xtra G7 mask packets rows sources gamma hg hh p n x bits hp
set_option hygiene false in
local notation "SFI" => ParamsV4.sfPW selector mask packets rows sources gamma hg hh p n x bits ph
set_option hygiene false in
local notation "KI" => KeptW.KSite selector xtra mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) modeI
set_option hygiene false in
local notation "KH0I" => (fun (_ : Fin UI) => (0 : Nat))
set_option hygiene false in
local notation "𝒞I" => skelCodeR mask packets rows sources resI hresI p kI rI ph (refill3 mask packets rows sources resI p kI rI seI spI eI (g7FI ph).2) (preFFI ph)

set_option hygiene false in
local notation "𝔨" => kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => rSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔘" => USite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔡" => dSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯𝔢𝔰" => resSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔙" => SourceBudget.Params.cVcN selector sources gamma hg hh p *
  RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "𝔒" => C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits
set_option hygiene false in
local notation "ℭℭ" => PCJda54a286946142d3_BranchPhases.cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "𝔠𝔞𝔭" => capC sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) x
  (C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
    (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits)

end rpsite

end
end NearCubicWires.SourceStart.C2RP
end

