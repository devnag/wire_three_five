import Proof.Packets.SrcEntryW

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
namespace NearCubicWires.SourceStart.EntryW
open NearCubicWires.SourceSkeleton.KeptW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW
noncomputable section

section site
variable (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔨" => kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => rSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔘" => USite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔙" => SourceBudget.Params.cVcN selector sources gamma hg hh p *
  RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "𝔒" => C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits
set_option hygiene false in
local notation "ℭ" => PCJda54a286946142d3_BranchPhases.cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "ℭ𝔖" => cacheSite selector xtra mask packets rows sources gamma hg hh p (USite selector xtra mask packets rows sources gamma hg hh p + 1) (Nat.le_succ _)
set_option hygiene false in
local notation "𝔠𝔞𝔭" => capC sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) x
  (C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
    (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits)

end site

end
end NearCubicWires.SourceStart.EntryW
end

