import Proof.SourceAssembly.SourceStepsNums
import Proof.SourceAssembly.SourceStepsClassR
import Proof.SourceAssembly.SourceStepsParamsV4
import Proof.SourceAssembly.SourceFirstSeam3B
import Proof.Packets.BudgetFirst3
import Proof.Packets.BudgetRefill3
import Proof.Packets.BudgetJ5Site
import Proof.Packets.BudgetSiteAbsorb

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
variable (printer : EightSources → WilliamsAlgorithm) (cVc hV : ParNat) (y yF0 I : ClsFam)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (capIndex : ParNat)

set_option hygiene false in
local notation "𝔅" => siteBIR printer cVc hV y yF0 I
set_option hygiene false in
local notation "ℜ" => siteRcR printer cVc hV y yF0
set_option hygiene false in
local notation "𝔏" => liveOfR (siteBIR printer cVc hV y yF0 I).hT sources gamma hg hh p
set_option hygiene false in
local notation "𝔨" => kSelR (baseR (siteBIR printer cVc hV y yF0 I)).ofBaseR capIndex sources gamma hg hh p

def zRef : CostCls :=
  ⟨y.dP sources gamma hg hh p, y.hT sources gamma hg hh p, y.hS sources gamma hg hh p 𝔏,
    y.cP sources gamma hg hh p 𝔨 + 0, y.cT sources gamma hg hh p 𝔨 + 1, y.cS sources gamma hg hh p 𝔨 + 0⟩

def zFirst : CostCls :=
  ⟨yF0.dP sources gamma hg hh p, yF0.hT sources gamma hg hh p, yF0.hS sources gamma hg hh p 𝔏,
    yF0.cP sources gamma hg hh p 𝔨 + 0 + 1, yF0.cT sources gamma hg hh p 𝔨 + 1, yF0.cS sources gamma hg hh p 𝔨 + 0⟩

theorem zRef_ex : ∃ n0, ∀ n, n0 ≤ n → ∀ free : ℕ,
    (zRef printer cVc hV y yF0 I sources gamma hg hh p capIndex).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) free →
      free + 2 ≤ (ℜ).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏 ((ℜ).hR sources gamma hg hh p)
        (C10PartsSchedule.widthAt sources 𝔨 n) :=
  windows_siteBIR printer cVc hV y yF0 I sources gamma hg hh p capIndex _
    (y_dP_le_siteBIR printer cVc hV y yF0 I sources gamma hg hh p)
    (siteRcR_conds printer cVc hV y yF0 sources gamma hg hh p).2.2.1

theorem zFirst_ex : ∃ n0, ∀ n, n0 ≤ n → ∀ free : ℕ,
    (zFirst printer cVc hV y yF0 I sources gamma hg hh p capIndex).In 4 𝔏 n (C10PartsSchedule.widthAt sources 𝔨 n) free →
      free + 2 ≤ (ℜ).C sources gamma hg hh p * RuntimeShape.tableClass 𝔏 ((ℜ).hR sources gamma hg hh p)
        (C10PartsSchedule.widthAt sources 𝔨 n) :=
  windows_siteBIR printer cVc hV y yF0 I sources gamma hg hh p capIndex _
    (yF0_dP_le_siteBIR printer cVc hV y yF0 I sources gamma hg hh p)
    (siteRcR_conds printer cVc hV y yF0 sources gamma hg hh p).2.2.2.1

/-- **The refill windows' onset.** -/
def refOn : ℕ := Classical.choose (zRef_ex printer cVc hV y yF0 I sources gamma hg hh p capIndex)
/-- **The first cycle's windows' onset.** -/
def firstOn : ℕ := Classical.choose (zFirst_ex printer cVc hV y yF0 I sources gamma hg hh p capIndex)

end generic

/-! ## At the site (`B = siteBP4`, `Rc` = the ClassV4 reserve, index `k = kSelR (baseR siteBP4).ofBaseR capIndex`) -/

section site
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (capIndex : ParNat)

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

/-- **`B`'s base RHS at index `k`** (the site's `refillCost = familyCost = firstCost`). -/
def Bsplit (k n : ℕ) : ℕ :=
  Admission.splitRHS ((baseR 𝔅4).dS sources gamma hg hh p) ((baseR 𝔅4).hT sources gamma hg hh p)
    ((baseR 𝔅4).hS sources gamma hg hh p) ((baseR 𝔅4).m sources gamma hg hh p) ((baseR 𝔅4).L sources gamma hg hh p)
    ((baseR 𝔅4).cP sources gamma hg hh p k) ((baseR 𝔅4).cT sources gamma hg hh p k) ((baseR 𝔅4).cS sources gamma hg hh p k) n
    (C10PartsSchedule.widthAt sources k n)

/-- **The refill rows' onset at the site** (fold into `xtra`). -/
def refOnS : ℕ := refOn printerOf (cVcN selector) (hVN selector) 𝔜4 𝔜𝔉4 𝔍4 sources gamma hg hh p capIndex
/-- **The first rows' onset at the site** (fold into `xtra`). -/
def firstOnS : ℕ := firstOn printerOf (cVcN selector) (hVN selector) 𝔜4 𝔜𝔉4 𝔍4 sources gamma hg hh p capIndex

end site

end
end NearCubicWires.SourceFactorSel.ClauseCost
end

