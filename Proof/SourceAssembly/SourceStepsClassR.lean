import Proof.SourceAssembly.SourceSkelClassR
import Proof.Packets.BudgetSiteAssembly
import Proof.Packets.BudgetSiteAbsorb

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton NearCubicWires.RuntimeShape NearCubicWires.Admission
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params
namespace NearCubicWires.SourceSkeleton.ClassR
noncomputable section

/-! ## 1. The family class, the ordered base and the clock condition at `rB` -/

/-- **The ordered base class at `rB`** of a family (`m := 4`, `L := liveOfR hT`). -/
def baseR (c : ClsFam) : SiteClassFam := SiteClassFam.orderedR c.dP c.hT c.hS c.cP c.cT c.cS

/-- `B.dS ≤ k` at the index `k = kSelR (ofBaseR B) capIndex …` (`k ≥ remDegR ≥ rB + B.dS`). -/
theorem dS_le_kSelR (B : SiteClassFam) (capIndex : ParNat) (sources : EightSources) (gamma : Real)
    (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    B.dS sources gamma hg hh p ≤ kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p := by
  have h1 : B.dS sources gamma hg hh p ≤ remDegR (SiteClassFam.ofBaseR B) sources gamma hg hh p := by
    unfold remDegR SiteClassFam.ofBaseR
    simp only
    omega
  have h2 : remDegR (SiteClassFam.ofBaseR B) sources gamma hg hh p ≤
      kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p := by
    unfold kSelR SourceParent.kOf ControllerCappedRuntime.hierarchyIndex WorkspaceSelectedEntryRuntime.degree
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  omega

/-- **The clock condition at `rB`** for the site class: its polynomial exponent is below `kSelR (ofBaseR (baseR …))`. -/
theorem site_dP_lt_kSelR (fam ref first : ClsFam) (capIndex : ParNat) (sources : EightSources) (gamma : Real)
    (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    (siteCls fam ref first).dP sources gamma hg hh p + 1 ≤
      kSelR (SiteClassFam.ofBaseR (baseR (siteCls fam ref first))) capIndex sources gamma hg hh p + 2 := by
  have := dS_le_kSelR (baseR (siteCls fam ref first)) capIndex sources gamma hg hh p
  show (siteCls fam ref first).dP sources gamma hg hh p + 1 ≤ _
  change (siteCls fam ref first).dP sources gamma hg hh p ≤ _ at this
  omega

section site
variable (printer : EightSources → WilliamsAlgorithm) (cVc hV : ParNat) (y yF0 I : ClsFam)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

theorem dP_lt_kSel_siteBIR (capIndex : ParNat) (d : ℕ) (hd : d ≤ (siteBIR printer cVc hV y yF0 I).dP sources gamma hg hh p) :
    d + 1 ≤ kSelR (SiteClassFam.ofBaseR (baseR (siteBIR printer cVc hV y yF0 I))) capIndex sources gamma hg hh p + 2 := by
  have hk : (siteBIR printer cVc hV y yF0 I).dP sources gamma hg hh p + 1 ≤
      kSelR (SiteClassFam.ofBaseR (baseR (siteBIR printer cVc hV y yF0 I))) capIndex sources gamma hg hh p + 2 :=
    site_dP_lt_kSelR (famSiteR printer cVc hV) (refFam (siteRcR printer cVc hV y yF0) y)
      (firstFam (siteRcR printer cVc hV y yF0) (yF0.join I)) capIndex sources gamma hg hh p
  omega

theorem y_dP_le_siteBIR : y.dP sources gamma hg hh p ≤ (siteBIR printer cVc hV y yF0 I).dP sources gamma hg hh p :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem yF0_dP_le_siteBIR : yF0.dP sources gamma hg hh p ≤ (siteBIR printer cVc hV y yF0 I).dP sources gamma hg hh p :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- **Every `Rc` window of an `Rc`-free class below `siteBI`**, past ONE onset after its live scale. -/
theorem windows_siteBIR (capIndex : ParNat) (z : CostCls) (hzd : z.dP ≤ (siteBIR printer cVc hV y yF0 I).dP sources gamma hg hh p)
    (hzT : z.hT + 2 ≤ (siteRcR printer cVc hV y yF0).hR sources gamma hg hh p) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ free : ℕ,
      z.In 4 (liveOfR (siteBIR printer cVc hV y yF0 I).hT sources gamma hg hh p) n
        (C10PartsSchedule.widthAt sources (kSelR (SiteClassFam.ofBaseR (baseR (siteBIR printer cVc hV y yF0 I))) capIndex sources gamma hg hh p) n)
        free →
      free + 2 ≤ (siteRcR printer cVc hV y yF0).C sources gamma hg hh p *
        tableClass (liveOfR (siteBIR printer cVc hV y yF0 I).hT sources gamma hg hh p) ((siteRcR printer cVc hV y yF0).hR sources gamma hg hh p)
          (C10PartsSchedule.widthAt sources (kSelR (SiteClassFam.ofBaseR (baseR (siteBIR printer cVc hV y yF0 I))) capIndex sources gamma hg hh p) n) := by
  obtain ⟨n0, h0⟩ := windows3_sat sources (kSelR (SiteClassFam.ofBaseR (baseR (siteBIR printer cVc hV y yF0 I))) capIndex sources gamma hg hh p)
    z 4 (liveOfR (siteBIR printer cVc hV y yF0 I).hT sources gamma hg hh p) (by decide)
    (dP_lt_kSel_siteBIR printer cVc hV y yF0 I sources gamma hg hh p capIndex z.dP hzd)
  exact ⟨n0, fun n hn free hf => h0 n hn free hf _ _ (siteRcR_conds printer cVc hV y yF0 sources gamma hg hh p).1 hzT⟩

end site

section windows

end windows

end
end NearCubicWires.SourceSkeleton.ClassR
end

