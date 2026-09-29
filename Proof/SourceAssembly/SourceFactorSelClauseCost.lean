import Proof.SourceAssembly.SourceStepsNums
import Proof.SourceAssembly.SourceStepsParamsV4

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceBudget NearCubicWires.SourceSkeleton.ClassR
open NearCubicWires.SourceConstruction NearCubicWires.SourceBudget.Params
namespace NearCubicWires.SourceFactorSel.ClauseCost
noncomputable section

section generic

set_option hygiene false in
local notation "𝔅" => siteBIR printer cVc hV y yF0 I
set_option hygiene false in
local notation "ℜ" => siteRcR printer cVc hV y yF0
set_option hygiene false in
local notation "𝔏" => liveOfR (siteBIR printer cVc hV y yF0 I).hT sources gamma hg hh p
set_option hygiene false in
local notation "𝔨" => kSelR (baseR (siteBIR printer cVc hV y yF0 I)).ofBaseR capIndex sources gamma hg hh p


end generic

/-! ## At the site (`B = siteBP4`, `Rc` = the ClassV4 reserve, index `k = kSelR (baseR siteBP4).ofBaseR capIndex`) -/

section site

set_option hygiene false in
local notation "𝔅4" => SourceSkeleton.ClassV4.siteBP4 selector mask packets rows
set_option hygiene false in
local notation "ℜ4" => SourceSkeleton.ClassV4.siteR4 selector mask packets rows
set_option hygiene false in
local notation "𝔏4" => SourceSkeleton.ClassV4.siteL4 selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔜4" => SourceSkeleton.ClassV4.siteY4 selector mask packets rows
set_option hygiene false in
local notation "𝔜𝔉4" => SourceSkeleton.ClassV4.siteYF04 selector mask packets rows
set_option hygiene false in
local notation "𝔍4" => SourceSkeleton.ClassV4.siteI4 selector mask packets rows


end site

end
end NearCubicWires.SourceFactorSel.ClauseCost
end

