import Proof.SourceAssembly.SourceStepsNums
import Proof.SourceAssembly.SourceStepsCallFacts
import Proof.SourceAssembly.SourceSkelLayoutW
import Proof.SourceAssembly.SourceSkelBridge
import Proof.Packets.BudgetWidthA
import Proof.Packets.BudgetSiteOrder
import Proof.Packets.SrcMetaIface2
import Proof.SourceAssembly.SourceSkelParamsV4
import Proof.SourceAssembly.SourceSkelFirstW
import Proof.CaseAnalysis.FinalEngineFuelSeam

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
namespace NearCubicWires.SourceStart.LayRP
noncomputable section

/-! ## 1. The onset of the load and the unit -/

/-- **Past one onset**, `201·K ≤ q` and `1 ≤ q / (200(K+2))` (`K = normalizedLiveCount q L ≤ L·logScale q`). -/
theorem lay_eventually (L : ℕ) : ∃ onset : ℕ, ∀ q, onset ≤ q →
    201 * normalizedLiveCount q L ≤ q ∧ 1 ≤ q / (200 * (normalizedLiveCount q L + 1 + 1)) := by
  obtain ⟨n0, hn0⟩ := SupplierCapacity.coefficient_mul_logScale_pow_eventually_le (201 * L + 400) 1
  refine ⟨n0, fun q hq => ?_⟩
  have h1 := hn0 q hq
  rw [pow_one] at h1
  have h2 : normalizedLiveCount q L ≤ L * logScale q := by
    unfold normalizedLiveCount
    exact Nat.min_le_right _ _
  have h3 := RepairSource.CloseoutFinal.C10EngineFuelSeam.one_le_logScale q
  set t := logScale q with ht
  set K := normalizedLiveCount q L with hK
  have e1 : (201 * L + 400) * t = 201 * (L * t) + 400 * t := by ring
  rw [e1] at h1
  refine ⟨by omega, ?_⟩
  rw [Nat.le_div_iff_mul_le (by positivity)]
  omega

/-! ## 2. The caps at a layout family (any mode) -/

section gen
variable (selector : CyclicChoice.Laws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
  (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L : ℕ)

/-! ## 3. The site's layout family -/

def layF (target : ℕ) (mode : Bool) (C degree den : ℕ) (hden0 : SourceSkeleton.layDen0 sources degree target L ≤ den)
    (hq0 : SourceSkeleton.layOnset sources degree target L ≤ q)
    (hA : ∀ j, Admission.Admitted den degree (SourceRequest.FactorLoop.factorsAt coordinate ph ci j))
    (h201 : 201 * normalizedLiveCount q L ≤ q) :
    TraceData.LayoutFamily coordinate ph ci sources L target mode selector :=
  SourceSkeleton.layOfW sources selector coordinate ph ci L target mode C (SourceBudget.wA q L)
    (SourceSkeleton.hadm_of_admission sources selector coordinate ph ci L target mode degree den hden0 hq0 hA)
    (fun j => (SourceSkeleton.hadm_of_admission sources selector coordinate ph ci L target mode degree den hden0 hq0 hA j).elim
      fun lay hw => hw ▸ SourceBudget.w_le_wA lay)
    (SourceBudget.wA_load q L h201)

end gen

/-! ## 4. The rows at the chain -/

section chain
variable (selector : CyclicChoice.Laws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
  (ph : Phase)
  (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
  (L : Nat)

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
local notation "PRj" => Packets.request sources L tgtC modeC (SourceRequest.FactorLoop.factorsAt coordC ph ci j)

end chain

/-! ## 5. The site: the onset and `layF`'s proofs -/

section site
variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

def layOnW : ℕ :=
  Classical.choose (SourceBudget.widthAt_ge_eventually sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p)
    (Classical.choose (lay_eventually (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p))))

theorem layOnW_spec (n : ℕ) (h : layOnW selector mask packets rows sources gamma hg hh p ≤ n) :
    201 * normalizedLiveCount (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n)
        (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p) ≤
      C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n ∧
    1 ≤ C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n /
      (200 * (normalizedLiveCount (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n)
        (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p) + 1 + 1)) :=
  Classical.choose_spec (lay_eventually (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)) _
    (Classical.choose_spec (SourceBudget.widthAt_ge_eventually sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p)
      (Classical.choose (lay_eventually (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)))) n h)

theorem layF_adm (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (n : ℕ)
    (hext : ParamsV4.extraW selector xtra mask packets rows sources gamma hg hh p ≤ n) :
    CloseoutWitnessPolicy.inputCutoff sources ≤ n ∧
    SourceSkeleton.layDen0 sources p.clauseDegree (SourceBudget.tgt sources p) (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p) ≤
      (ParamsV4.fPW selector xtra mask packets rows).capIndex sources gamma hg hh p + 1 ∧
    SourceSkeleton.layOnset sources p.clauseDegree (SourceBudget.tgt sources p) (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p) ≤
      C10PartsSchedule.widthAt sources (FirstW.kSite selector xtra mask packets rows sources gamma hg hh p) n := by
  refine ⟨le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hext), ?_, ?_⟩
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (SourceBudget.den0_le (ParamsV4.den0W selector mask packets rows) sources gamma hg hh p)
  · exact le_trans (le_max_left _ _) (ParamsV4.qOnW_le_width selector mask packets rows xtra sources gamma hg hh p n hext)

end site

end
end NearCubicWires.SourceStart.LayRP
end

