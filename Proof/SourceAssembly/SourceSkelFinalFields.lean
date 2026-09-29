import Mathlib
import Proof.SourceAssembly.SourceFactorSelTraceSite
import Proof.SourceAssembly.SourceRequestSelKeptNums
import Proof.SourceAssembly.SourceRequestSelStripLen
import Proof.SourceAssembly.SourceSkelFinalClose2
import Proof.SourceAssembly.SourceSkelSiteResid
import Proof.SourceAssembly.SourceStepsSeam6

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
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSkeleton
open NearCubicWires.SourceSkeleton.FirstW NearCubicWires.SourceStart.EntryW
namespace NearCubicWires.SourceSkeleton.Final
open NearCubicWires.SourceSteps
open NearCubicWires.SourceSkeleton.FirstW NearCubicWires.SourceStart.EntryW
noncomputable section

section fields

set_option hygiene false in
local notation "CODE" => skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows)
  (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows))
  (ParamsV4.fPW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows)
  (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _
    (FirstW.g7OfW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows)) (FirstW.firstW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows)
set_option hygiene false in
local notation "𝔉" => forcedChoices mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows)
set_option hygiene false in
local notation "denI" => (𝔉).capIndex sources gamma hg hh p + 1
set_option hygiene false in
local notation "kI" => kSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "rI" => rSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p
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
local notation "eI" => eSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "hresI" => resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows) sources gamma hg hh p
set_option hygiene false in
local notation "g7FI" => fun ph' => FirstW.g7OfW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows sources gamma hg hh p modeI ph'
set_option hygiene false in
local notation "preFFI" => fun ph' => FirstW.firstW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows sources gamma hg hh p modeI ph'
set_option hygiene false in
local notation "siteI" => (CODE).site sources gamma hg hh p
set_option hygiene false in
local notation "EtI" => EWFam selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows (CODE) sources gamma hg hh p n x bits hp
set_option hygiene false in
local notation "EFI" => EFSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows sources gamma hg hh p n x bits hp
set_option hygiene false in
local notation "SFI" => ParamsV4.sfPW selector mask packets rows sources gamma hg hh p n x bits ph
set_option hygiene false in
local notation "KI" => KeptW.KSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) modeI
set_option hygiene false in
local notation "KH0I" => (fun (_ : Fin UI) => (0 : Nat))
set_option hygiene false in
local notation "𝒞I" => skelCodeR mask packets rows sources resI hresI p kI rI ph (refill3 mask packets rows sources resI p kI rI seI spI eI (g7FI ph).2) (preFFI ph)

set_option hygiene false in
local notation "𝔛" => NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector
set_option hygiene false in
local notation "vQI" => (req sources kI (PolynomialClock.ordinaryClock kI) x oracleI).arity
set_option hygiene false in
local notation "capCI" => capC sources kI (PolynomialClock.ordinaryClock kI) x oracleI
set_option hygiene false in
local notation "BTSI" => ControllerSelectedContinuation.bodyTapes sources p kI rI (scratchOf mask packets rows sources resI)

open NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open PCJ515eaa990d75455b_FamilyInit

set_option hygiene false in
local notation "𝔇I" => dimsOf mask packets rows sources resI p kI rI
set_option hygiene false in
local notation "𝒽I" => UOf_le mask packets rows sources resI p kI rI
set_option hygiene false in
local notation "codeFI" => fun ph' => skelCodeR mask packets rows sources resI hresI p kI rI ph' (refill3 mask packets rows sources resI p kI rI seI spI eI (g7FI ph').2) (preFFI ph')
set_option hygiene false in
local notation "layI" => layFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph ci
set_option hygiene false in
local notation "K0I" => K0FS selector mask packets rows sources gamma hg hh p n x bits hn hp ph ci
set_option hygiene false in
local notation "dfltI" => dfltFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph
set_option hygiene false in
local notation "costI" => costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph
set_option hygiene false in
local notation "oldI" => (fun j => if j = 0 then (A ((𝒞I).whole (Dims.encT (d := dimsOf mask packets rows sources resI p kI rI) (UOf_le mask packets rows sources resI p kI rI) 5).castSucc)).take (InitRun.D0 bI)
  else oldAt coordI ph ci sources LI tgtI modeI bI (InitRun.D0 bI) j)
set_option hygiene false in
local notation "HdZI" => (fun (_ : Nat) (_ : Fin UI) => (0 : Nat))
set_option hygiene false in
local notation "AdZI" => (fun (_ : Nat) (_ : Fin UI) => ([] : List Bool))
set_option hygiene false in
local notation "vdI" => clauseVals mask selector packets rows compiler sources p (denI) (Nat.succ_pos _) kI rI (scratchOf mask packets rows sources resI) n x bits hp siteI codeFI ph ci LI layI
  (degOf sources selector coordI ph ci LI tgtI modeI layI) VI dfltI (InitRun.D0 bI) (InitRun.cap0 bI) (CloseoutFinalC10AppendWorkspaceInit.capacity bI)
  (CloseoutFinalC10AppendWorkspaceInit.capacity bI) oldI HdZI AdZI RcI costI costI costI RcI
set_option hygiene false in
local notation "capsI" => capsSite mask packets rows sources hg hh p kI n
set_option hygiene false in
local notation "layAI" => layoutAtOf sources selector coordI ph ci LI tgtI modeI layI
set_option hygiene false in
local notation "factsAI" => factsAtOf sources selector compiler coordI ph ci LI tgtI modeI
set_option hygiene false in
local notation "gWI" => (DSite selector mask packets rows sources gamma hg hh p).gW
set_option hygiene false in
local notation "NNI" => (vdI).entries.length

end fields

end
end NearCubicWires.SourceSkeleton.Final
end

