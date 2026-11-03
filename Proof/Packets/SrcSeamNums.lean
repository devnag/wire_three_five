import Proof.SourceAssembly.SourceStepsNums
import Proof.SourceAssembly.SourceStepsF6
import Proof.SourceAssembly.SourceStepsCallFacts
import Proof.SourceAssembly.SourceStepsParamsV4
import Proof.Packets.BudgetEntryCount
import Proof.SourceAssembly.SourceStepsSat
import Proof.SourceAssembly.SourceSkelXtraF

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
open NearCubicWires.SourceSteps
namespace NearCubicWires.SourceStart.SeamRP
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-! ## The onset -/

section onset
variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

def seamOn (k den : ℕ) (hden : 1 ≤ den) : ℕ :=
  max (Classical.choose (ClassV4.seam_scalars_Rc4 selector mask packets rows sources gamma hg hh p k))
    (max (Classical.choose (ClassV4.seam_call_Rc4 selector mask packets rows sources gamma hg hh p k den hden))
      (max (Classical.choose (SourceBudget.widthAt_ge_eventually sources k
          (Classical.choose (SourceSteps.enc_sat_at sources k (SourceSteps.rBsel sources p)
            (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)))))
        (SourceSteps.selR sources p k).onset))

/-- **The seam rows' onset at the site** (index `kW`, denominator the fill's cap index `+ 1`), an `XtraW`-shaped onset to fold into `xtra`. -/
def seamOnW : ℕ :=
  seamOn selector mask packets rows sources gamma hg hh p (ParamsV4.kW selector mask packets rows sources gamma hg hh p)
    ((ParamsV4.fPW selector (XtraF.xtraF selector) mask packets rows).capIndex sources gamma hg hh p + 1) (Nat.succ_pos _)

end onset

/-! ## The entry-count helpers (at `N = |phaseE … ci|`) -/

section helpers

end helpers

section nums
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

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
local notation "vdC" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw (oldAt coordC ph ci sources L tgtC modeC b Dw) Hd Ad Rc familyCost refillCost firstCost counterReserve

set_option hygiene false in
local notation "vdX" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve

set_option hygiene false in
local notation "𝔏𝔖" => ClassV4.siteL4 selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "ℜ𝔖" => (ClassV4.siteR4 selector mask packets rows).C sources gamma hg hh p *
  RuntimeShape.tableClass (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)
    ((ClassV4.siteR4 selector mask packets rows).hR sources gamma hg hh p) (C10PartsSchedule.widthAt sources k n)

end nums

end
end NearCubicWires.SourceStart.SeamRP
end

