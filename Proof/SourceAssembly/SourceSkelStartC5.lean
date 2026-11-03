import Proof.SourceAssembly.SourceSkelStartC
import Proof.SourceAssembly.SourceSkelStartB5
import Proof.SourceAssembly.SourceStepsFirstOut5

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceSkeleton.StartC5
open NearCubicWires.SourceSkeleton.StartC
open NearCubicWires.SourceSkeleton.KeptW NearCubicWires.SourceSkeleton.GuardG NearCubicWires.SourceStart.EntryW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge NearCubicWires.SourceSteps
open PCJ515eaa990d75455b_FamilyInit
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section site
variable (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔨" => kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => rSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯𝔢𝔰" => resSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔰" => scrSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔘" => USite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔡" => dSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯
set_option hygiene false in
local notation "𝒽1" => UOf_le_succ mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯
set_option hygiene false in
local notation "𝔮" => C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n
set_option hygiene false in
local notation "𝔏" => LW selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "ℜ" => Once.Rc (hRx4 selector mask packets rows sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p) 1 (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "𝔙" => SourceBudget.Params.cVcN selector sources gamma hg hh p *
  RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden 𝔨 𝔯 𝔰 n x bits hp
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "vQ" => (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC).arity
set_option hygiene false in
local notation "layA" => layoutAtOf sources selector coordC ph ci 𝔏 tgtC modeC lay
set_option hygiene false in
local notation "factsA" => factsAtOf sources selector compiler coordC ph ci 𝔏 tgtC modeC
set_option hygiene false in
local notation "vWS" => P1TopDownPaidReusableReserves.workspace (printerOf sources) 𝔙
set_option hygiene false in
local notation "vRW" => P1TopDownPaidReusableReserves.rewind (printerOf sources) 𝔙
set_option hygiene false in
local notation "vBF" => P1TopDownPaidReusableReserves.buffer 𝔙
set_option hygiene false in
local notation "vMB" => InitRun.Mb 𝔏 vQ
set_option hygiene false in
local notation "vMS" => InitPost.Ms 𝔏 vQ
set_option hygiene false in
local notation "vU0" => InitRun.U0 𝔏 vQ
set_option hygiene false in
local notation "ℭ𝔖" => cacheSite selector xtra mask packets rows sources gamma hg hh p (USite selector xtra mask packets rows sources gamma hg hh p + 1) (Nat.le_succ _)
set_option hygiene false in
local notation "𝔔" => q284Site selector xtra mask packets rows sources gamma hg hh p (USite selector xtra mask packets rows sources gamma hg hh p + 1) (Nat.le_succ _)
set_option hygiene false in
local notation "𝔟" => C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n
set_option hygiene false in
local notation "𝔠𝔞𝔭" => capC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC
set_option hygiene false in
local notation "𝔴𝔮" => ZeroPadding.pad 𝔠𝔞𝔭 (SourceSteps.qwordAt sources p 𝔨 n x bits ci.val)
set_option hygiene false in
local notation "preFF" => fun ph' => firstW selector xtra G7 mask packets rows sources gamma hg hh p modeC ph'
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph).2) (preFF ph)
set_option hygiene false in
local notation "codeF" => fun ph' => skelCodeR mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph' (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp (eSite selector xtra mask packets rows sources gamma hg hh p) (g7F ph').2) (preFF ph')
set_option hygiene false in
local notation "vdS0" => clauseVals mask selector packets rows compiler sources p den hden 𝔨 𝔯 𝔰 n x bits hp site codeF ph ci 𝔏 lay (degOf sources selector coordC ph ci 𝔏 tgtC modeC lay) 𝔙 dflt (InitRun.D0 𝔟) (InitRun.cap0 𝔟) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝔟) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝔟) (fun j => if j = 0 then [] else oldAt coordC ph ci sources 𝔏 tgtC modeC 𝔟 (InitRun.D0 𝔟) j) Hd Ad ℜ familyCost refillCost firstCost counterReserve
set_option hygiene false in
local notation "𝔦𝔠" => InitS.initAllXCostE (plSite selector xtra mask packets rows sources gamma hg hh p modeC ph) 𝔏 1
  (SourceBudget.Params.cVcN selector sources gamma hg hh p) (sC sources gamma hg hh p)
  (rC sources gamma hg hh p) (pE sources gamma hg hh p) (pC sources gamma hg hh p) 3 1 (ldE sources gamma hg hh p)
  (ldC sources gamma hg hh p) modeC (SourceBudget.Params.tgOf sources gamma hg hh p) 𝔮 𝔟 (dE sources gamma hg hh p)
  (dC sources gamma hg hh p) (cwE sources gamma hg hh p) (cwC sources gamma hg hh p)
  (NearCubicWires.SourceStart.MetaStepGF.metaCostG selector sources p packets 𝔏 𝔮) + 2

end site

end
end NearCubicWires.SourceSkeleton.StartC5
end

