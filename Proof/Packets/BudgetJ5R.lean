import Proof.SourceAssembly.SourceSkelGen
import Proof.SourceAssembly.SourceStepsSelect

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceBudget
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-! ## 1. The live scale and the classes at `rB` -/

/-- **The live scale at `rB`**: `L = rB + (rB + hT) + σ + 2`. -/
def liveOfR (hT : ParNat) : ParNat := fun sources gamma hg hh p =>
  SourceSteps.rBsel sources p + (SourceSteps.rBsel sources p + hT sources gamma hg hh p) + SelectedRuntime.sigma sources + 2

/-- **The ordered base class at `rB`**: divisor `4`, live scale `liveOfR hT`. -/
def SiteClassFam.orderedR (dS hT : ParNat)
    (hS : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → ℕ)
    (cP cT cS : ParCoef) : SiteClassFam where
  dS := dS
  hT := hT
  hS := fun sources gamma hg hh p => hS sources gamma hg hh p (liveOfR hT sources gamma hg hh p)
  m := fun _ _ _ _ _ => 4
  L := liveOfR hT
  cP := cP
  cT := cT
  cS := cS

/-- **The site class from a base class at `rB`** (`ofBase` with `rSel ↦ rB`). -/
def SiteClassFam.ofBaseR (B : SiteClassFam) : SiteClassFam where
  dS := fun sources gamma hg hh p => SourceSteps.rBsel sources p + B.dS sources gamma hg hh p
  hT := fun sources gamma hg hh p => SourceSteps.rBsel sources p + B.hT sources gamma hg hh p
  hS := fun sources gamma hg hh p => SourceSteps.rBsel sources p + B.hS sources gamma hg hh p
  m := B.m
  L := B.L
  cP := fun sources gamma hg hh p k => B.cP sources gamma hg hh p k +
    C10PartsSchedule.widthConst sources k^SourceSteps.rBsel sources p*
      (B.cP sources gamma hg hh p k + B.cP sources gamma hg hh p k + 4) + 4
  cT := fun sources gamma hg hh p k => B.cT sources gamma hg hh p k +
    C10PartsSchedule.widthConst sources k^SourceSteps.rBsel sources p*(B.cT sources gamma hg hh p k + B.cT sources gamma hg hh p k)
  cS := fun sources gamma hg hh p k => B.cS sources gamma hg hh p k +
    C10PartsSchedule.widthConst sources k^SourceSteps.rBsel sources p*(B.cS sources gamma hg hh p k + B.cS sources gamma hg hh p k)

/-! ## 2. The J5 free choices at `rB` -/

/-- **The recipe's source degree at `rB`** (`remDeg` with `rSel ↦ rB`). -/
def remDegR (Q : SiteClassFam) (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) : ℕ :=
  SourceSteps.rBsel sources p + (Q.dS sources gamma hg hh p + SourceSteps.rBsel sources p +
    reqE sources p*PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources) +
    5*(SourceSteps.rBsel sources p + SourceSteps.rBsel sources p) +
    2*((SourceSteps.rBsel sources p + SourceSteps.rBsel sources p) + SourceSteps.rBsel sources p) +
    (SourceSteps.rBsel sources p + reqE sources p*PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources)))

/-- The hierarchy index at `rB`. -/
abbrev kSelR (Q : SiteClassFam) (capIndex : ParNat)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  SourceParent.kOf capIndex (remDegR Q) sources gamma hg hh p

/-- The J5 constants at `rB`. -/
def constsOfR (Q : SiteClassFam) (capIndex : ParNat)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    J5Consts :=
  sourceConsts sources (kSelR Q capIndex sources gamma hg hh p) p (SourceSteps.rBsel sources p)
    (Q.dS sources gamma hg hh p) (Q.hT sources gamma hg hh p) (Q.hS sources gamma hg hh p)
    (Q.m sources gamma hg hh p) (Q.L sources gamma hg hh p)
    (Q.cP sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))
    (Q.cT sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))
    (Q.cS sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))

def j5FreeR (Q : SiteClassFam) (capIndex base : ParNat) : FreeChoices where
  capIndex := capIndex
  remainingDegree := remDegR Q
  r := fun sources _ _ _ p => SourceSteps.rBsel sources p
  base := base
  remainingFuel := fun sources gamma hg hh p n =>
    (constsOfR Q capIndex sources gamma hg hh p).fuel (CloseoutLanguage.selectedPCPP sources) n
      (C10PartsSchedule.widthAt sources (kSelR Q capIndex sources gamma hg hh p) n)
  remainingCoefficient := fun _ _ _ _ _ => 0
  remainingOnset := fun _ _ _ _ _ => 0
  tableCoefficient := fun _ _ _ _ _ => 0
  tableDegree := fun _ _ _ _ _ => 0

def sfOfR (B : SiteClassFam) (capIndex : ParNat) : SiteFuelFam :=
  fun sources gamma hg hh p n _ _ _ =>
    siteRHS sources (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p) (SourceSteps.rBsel sources p)
      (B.dS sources gamma hg hh p) (B.hT sources gamma hg hh p) (B.hS sources gamma hg hh p)
      (B.m sources gamma hg hh p) (B.L sources gamma hg hh p)
      (B.cP sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p))
      (B.cT sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p))
      (B.cS sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p)) n
      (C10PartsSchedule.widthAt sources (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p) n)

/-- **`base` at `rB`**: `selR`'s onset at the recipe's index, maxed with the admission onset `extra`. -/
def baseOfR (B : SiteClassFam) (capIndex extra : ParNat) : ParNat := fun sources gamma hg hh p =>
  max (SourceSteps.selR sources p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p)).onset
    (extra sources gamma hg hh p)

/-- Every admission onset `extra` is below `base`. -/
theorem extra_le_baseR (B : SiteClassFam) (capIndex extra : ParNat) (sources : EightSources) (gamma : Real)
    (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    extra sources gamma hg hh p ≤ baseOfR B capIndex extra sources gamma hg hh p :=
  le_max_right _ _

abbrev fOrdGR (dS hT : ParNat) (hS cP cT cS : ParCoef) (den0 extra : ParNat) : FreeChoices :=
  j5FreeR (SiteClassFam.ofBaseR (SiteClassFam.orderedR dS hT hS cP cT cS)) (capIndexOf den0)
    (baseOfR (SiteClassFam.orderedR dS hT hS cP cT cS) (capIndexOf den0) extra)

abbrev sfOrdGR (dS hT : ParNat) (hS cP cT cS : ParCoef) (den0 : ParNat) : SiteFuelFam :=
  sfOfR (SiteClassFam.orderedR dS hT hS cP cT cS) (capIndexOf den0)

section j5

end j5

end
end NearCubicWires.SourceBudget
end

