import Proof.SourceAssembly.SourceSkelParamsR
import Proof.SourceAssembly.SourceSkelProt
import Proof.SourceAssembly.SourceStepsParamsV4

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
namespace NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsR (inCR inER gWR)
noncomputable section

variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)

/-! ## 1. The site class and its live scale at `rB` (v3) -/

/-- The site class (B7). -/
abbrev BW : SourceBudget.ClsFam := siteBP4 selector mask packets rows

/-- **The live scale at `rB`** (`= siteLR`, `siteLR_eq`). -/
def LW : SourceBudget.ParNat := SourceBudget.liveOfR (BW selector mask packets rows).hT

theorem one_le_LW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) : 1 ≤ LW selector mask packets rows sources gamma hg hh p := by
  unfold LW SourceBudget.liveOfR; omega

/-- The site's accuracy target. -/
abbrev TW : SourceBudget.ParNat := SourceBudget.Params.tgOf

/-! ## 2. `den0` -/

def smallDen0W (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  Classical.choose (Admission.small_poly selector (decompositionOf sources) p.clauseDegree (TW sources gamma hg hh p)
    (LW selector mask packets rows sources gamma hg hh p) (SourceBudget.DmOf packets rows SourceBudget.Params.degOf sources gamma hg hh p) 4
    (one_le_LW selector mask packets rows sources gamma hg hh p) (by decide))

/-- AD's `small_poly` arity onset (same data). -/
def smallOnsetW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  Classical.choose (Classical.choose_spec (Admission.small_poly selector (decompositionOf sources) p.clauseDegree
    (TW sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p)
    (SourceBudget.DmOf packets rows SourceBudget.Params.degOf sources gamma hg hh p) 4
    (one_le_LW selector mask packets rows sources gamma hg hh p) (by decide)))

/-- **`den0` at `rB`.** -/
def den0W : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat :=
  fun mask packets rows s g hg hh p =>
    max 1 (max (layDen0 s p.clauseDegree (TW s g hg hh p) (LW selector mask packets rows s g hg hh p))
      (smallDen0W selector mask packets rows s g hg hh p))

abbrev BordW : SourceBudget.SiteClassFam :=
  SourceBudget.SiteClassFam.orderedR (BW selector mask packets rows).dP (BW selector mask packets rows).hT
    (BW selector mask packets rows).hS (BW selector mask packets rows).cP (BW selector mask packets rows).cT
    (BW selector mask packets rows).cS

/-- **The hierarchy index at `rB`.** -/
abbrev kW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  SourceBudget.kSelR (SourceBudget.SiteClassFam.ofBaseR (BordW selector mask packets rows))
    (SourceBudget.capIndexOf (den0W selector mask packets rows)) sources gamma hg hh p

/-- `B`'s polynomial exponent lies below the index. -/
theorem BW_dP_le_kW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    (BW selector mask packets rows).dP sources gamma hg hh p ≤ kW selector mask packets rows sources gamma hg hh p := by
  have h1 : (BW selector mask packets rows).dP sources gamma hg hh p ≤
      SourceBudget.remDegR (SourceBudget.SiteClassFam.ofBaseR (BordW selector mask packets rows)) sources gamma hg hh p := by
    simp only [SourceBudget.remDegR, SourceBudget.SiteClassFam.ofBaseR, SourceBudget.SiteClassFam.orderedR, BordW, BW]
    omega
  have h2 : SourceBudget.remDegR (SourceBudget.SiteClassFam.ofBaseR (BordW selector mask packets rows)) sources gamma hg hh p ≤
      kW selector mask packets rows sources gamma hg hh p := by
    unfold kW SourceBudget.kSelR SourceParent.kOf ControllerCappedRuntime.hierarchyIndex WorkspaceSelectedEntryRuntime.degree
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  omega

/-! ## 3. The init's windows at `rB` -/

def initOnsetW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  @dite ℕ (∃ q0, ∀ q, q0 ≤ q → InitWin (hRx4 selector mask packets rows sources gamma hg hh p)
      (SourceBudget.Params.hVN selector sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p)
      (SourceBudget.Params.cVcN selector sources gamma hg hh p) (sC sources gamma hg hh p) (rC sources gamma hg hh p)
      (ldC sources gamma hg hh p) (ldE sources gamma hg hh p) (TW sources gamma hg hh p) q)
    (Classical.propDecidable _) (fun h => Classical.choose h) (fun _ => 0)

/-! ## 4. `extra` at `rB` -/

def aMW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  2^20 + dC sources gamma hg hh p + ldC sources gamma hg hh p + pC sources gamma hg hh p + cwC sources gamma hg hh p +
    SourceBudget.Params.cVcN selector sources gamma hg hh p + SourceBudget.Params.hVN selector sources gamma hg hh p +
    hRx4 selector mask packets rows sources gamma hg hh p + sC sources gamma hg hh p + rC sources gamma hg hh p +
    TW sources gamma hg hh p + LW selector mask packets rows sources gamma hg hh p +
    (inCR sources gamma hg hh p + 4 * LW selector mask packets rows sources gamma hg hh p) +
    C10PartsSchedule.thresholdFloor sources + NearCubicWires.SourceSkeleton.ClassV3.gCv3 selector mask packets rows sources gamma hg hh p

def eMW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  8 + dE sources gamma hg hh p + ldE sources gamma hg hh p + pE sources gamma hg hh p + cwE sources gamma hg hh p +
    SourceSteps.rBsel sources p + SourceBudget.Params.hVN selector sources gamma hg hh p +
    hRx4 selector mask packets rows sources gamma hg hh p + inER sources gamma hg hh p +
    NearCubicWires.SourceSkeleton.ClassV3.gEv3 selector mask packets rows sources gamma hg hh p

/-- **The arity onset at `rB`**: AD's layout and small onsets, SS's `enc_sat` at `rB`, the master window, `2^(2L+16)`, the init's windows. -/
def qOnW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  max (layOnset sources p.clauseDegree (TW sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p))
    (max (smallOnsetW selector mask packets rows sources gamma hg hh p)
      (max (Classical.choose (SourceSteps.enc_sat sources (SourceSteps.rBsel sources p) (LW selector mask packets rows sources gamma hg hh p)))
        (max (Classical.choose (SourceBudget.poly_le_Rc (aMW selector mask packets rows sources gamma hg hh p)
            (eMW selector mask packets rows sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p)))
          (max (2^(2 * LW selector mask packets rows sources gamma hg hh p + 16))
            (initOnsetW selector mask packets rows sources gamma hg hh p)))))

/-- The master window class at `rB`: `famSiteR ⊔ y ⊔ yF0`, coefficients `×64 + 64`, at `LW` and `kW`. -/
def zMW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    SourceBudget.CostCls :=
  let c := (((famSiteR printerOf (SourceBudget.Params.cVcN selector) (SourceBudget.Params.hVN selector)).join
      (siteY4 selector mask packets rows)).join (siteYF04 selector mask packets rows)).at sources gamma hg hh p
    (LW selector mask packets rows sources gamma hg hh p) (kW selector mask packets rows sources gamma hg hh p)
  ⟨c.dP, c.hT, c.hS, 64 * c.cP + 64, 64 * c.cT + 64, 64 * c.cS + 64⟩

theorem zMW_dP (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    (zMW selector mask packets rows sources gamma hg hh p).dP + 1 ≤ kW selector mask packets rows sources gamma hg hh p + 2 := by
  have hk := BW_dP_le_kW selector mask packets rows sources gamma hg hh p
  have hle : (zMW selector mask packets rows sources gamma hg hh p).dP ≤ (BW selector mask packets rows).dP sources gamma hg hh p := by
    simp only [zMW, SourceBudget.ClsFam.at, SourceBudget.ClsFam.join, BW, siteBP4, siteBIR, SourceBudget.siteCls,
      SourceBudget.refFam, SourceBudget.firstFam]
    omega
  omega

def winOnW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  Classical.choose (SourceBudget.windows3_sat sources (kW selector mask packets rows sources gamma hg hh p)
    (zMW selector mask packets rows sources gamma hg hh p) 4 (LW selector mask packets rows sources gamma hg hh p) (by decide)
    (zMW_dP selector mask packets rows sources gamma hg hh p))

def resOnW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  Classical.choose (SourceBudget.reserves_le_Rc (printerOf sources) sources (kW selector mask packets rows sources gamma hg hh p)
    (LW selector mask packets rows sources gamma hg hh p) (SourceBudget.Params.cVcN selector sources gamma hg hh p)
    (SourceBudget.Params.hVN selector sources gamma hg hh p))

def extraCoreW : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat :=
  fun mask packets rows s g hg hh p =>
    max (CloseoutWitnessPolicy.inputCutoff s)
      (max (2 ^ (CloseoutLanguage.selectedPCPP s).minimumArity)
        (max (Classical.choose (SourceBudget.widthAt_ge_eventually s (kW selector mask packets rows s g hg hh p)
            (qOnW selector mask packets rows s g hg hh p)))
          (max (winOnW selector mask packets rows s g hg hh p) (resOnW selector mask packets rows s g hg hh p))))

def extraW (xtra : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat) : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat :=
  fun mask packets rows s g hg hh p => max (extraCoreW selector mask packets rows s g hg hh p) (xtra mask packets rows s g hg hh p)

theorem xtra_le_extraW (xtra : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    xtra mask packets rows sources gamma hg hh p ≤ extraW selector xtra mask packets rows sources gamma hg hh p :=
  le_max_right _ _

/-- **Past `extraW`, the arity at the J5 index is past `qOnW`.** -/
theorem qOnW_le_width (xtra : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat) (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma)
    (n : ℕ) (hn : extraW selector xtra mask packets rows sources gamma hg hh p ≤ n) :
    qOnW selector mask packets rows sources gamma hg hh p ≤
      C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n :=
  Classical.choose_spec (SourceBudget.widthAt_ge_eventually sources (kW selector mask packets rows sources gamma hg hh p)
    (qOnW selector mask packets rows sources gamma hg hh p)) n
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hn))))

/-! ## 5. The reduce term -/

abbrev fPW (xtra : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) : FreeChoices :=
  SourceBudget.fOrdGR (siteBP4 selector mask packets rows).dP (siteBP4 selector mask packets rows).hT
    (siteBP4 selector mask packets rows).hS (siteBP4 selector mask packets rows).cP (siteBP4 selector mask packets rows).cT
    (siteBP4 selector mask packets rows).cS (den0W selector mask packets rows) (extraW selector xtra mask packets rows)

abbrev sfPW (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) : SiteFuelFam :=
  SourceBudget.sfOrdGR (siteBP4 selector mask packets rows).dP (siteBP4 selector mask packets rows).hT
    (siteBP4 selector mask packets rows).hS (siteBP4 selector mask packets rows).cP (siteBP4 selector mask packets rows).cT
    (siteBP4 selector mask packets rows).cS (den0W selector mask packets rows)

end
end NearCubicWires.SourceSkeleton.ParamsV4
end

