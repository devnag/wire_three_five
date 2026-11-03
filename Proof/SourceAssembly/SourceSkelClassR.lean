import Proof.Packets.SourceParams
import Proof.Packets.BudgetJ5R

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton.ClassR
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.SourceConstruction
noncomputable section

/-! ## 1. The generic class data at `rB` -/

/-- **The family class family at `rB`** (`famFam` with the record exponent `rBsel`). -/
def famFamR (printer : EightSources → WilliamsAlgorithm) (cVc hV dC : ParNat) : ClsFam where
  dP := fun s g hg hh p => (famClsAt (printer s) s p 0 (SourceSteps.rBsel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).dP
  hT := fun s g hg hh p => (famClsAt (printer s) s p 0 (SourceSteps.rBsel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).hT
  hS := fun s g hg hh p _ => (famClsAt (printer s) s p 0 (SourceSteps.rBsel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).hS
  cP := fun s g hg hh p k => (famClsAt (printer s) s p k (SourceSteps.rBsel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).cP
  cT := fun s g hg hh p k => (famClsAt (printer s) s p k (SourceSteps.rBsel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).cT
  cS := fun s g hg hh p k => (famClsAt (printer s) s p k (SourceSteps.rBsel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).cS

/-- The family class at `Dw`'s coefficient `22`, at `rB`. -/
abbrev famSiteR (printer : EightSources → WilliamsAlgorithm) (cVc hV : ParNat) : ClsFam :=
  famFamR printer cVc hV (fun _ _ _ _ _ => 22)

/-- **The site's reserve at `rB`**: `C = 1`, `hR` = the largest table exponent among the family class (at `rB`), the two cycle classes and
`V`, plus `2`. -/
def siteRcR (printer : EightSources → WilliamsAlgorithm) (cVc hV : ParNat) (y yF : ClsFam) : RcChoice where
  C := fun _ _ _ _ _ => 1
  hR := fun s g hg hh p => max (max ((famSiteR printer cVc hV).hT s g hg hh p) (y.hT s g hg hh p))
    (max (yF.hT s g hg hh p) (hV s g hg hh p)) + 2

def siteBIR (printer : EightSources → WilliamsAlgorithm) (cVc hV : ParNat) (y yF0 I : ClsFam) : ClsFam :=
  siteCls (famSiteR printer cVc hV) (refFam (siteRcR printer cVc hV y yF0) y) (firstFam (siteRcR printer cVc hV y yF0) (yF0.join I))

/-- The reserve's side conditions at `rB`. -/
theorem siteRcR_conds (printer : EightSources → WilliamsAlgorithm) (cVc hV : ParNat) (y yF : ClsFam)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    1 ≤ (siteRcR printer cVc hV y yF).C sources gamma hg hh p ∧
    (famSiteR printer cVc hV).hT sources gamma hg hh p + 2 ≤ (siteRcR printer cVc hV y yF).hR sources gamma hg hh p ∧
    y.hT sources gamma hg hh p + 2 ≤ (siteRcR printer cVc hV y yF).hR sources gamma hg hh p ∧
    yF.hT sources gamma hg hh p + 2 ≤ (siteRcR printer cVc hV y yF).hR sources gamma hg hh p ∧
    hV sources gamma hg hh p + 2 ≤ (siteRcR printer cVc hV y yF).hR sources gamma hg hh p :=
  ⟨le_rfl, Nat.add_le_add_right (le_trans (le_max_left _ _) (le_max_left _ _)) 2,
    Nat.add_le_add_right (le_trans (le_max_right _ _) (le_max_left _ _)) 2,
    Nat.add_le_add_right (le_trans (le_max_left _ _) (le_max_right _ _)) 2,
    Nat.add_le_add_right (le_trans (le_max_right _ _) (le_max_right _ _)) 2⟩

/-! ## 2. The concrete class data at `rB` -/

section site


end site
end
end NearCubicWires.SourceSkeleton.ClassR
end

