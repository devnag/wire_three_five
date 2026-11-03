import Proof.Packets.BudgetBaseAssembly
import Proof.Packets.BudgetFirst3
import Proof.Packets.BudgetTableOnset
import Proof.SourceAssembly.SourcePhaseFuel

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
open NearCubicWires.SourceSkeleton NearCubicWires.RuntimeShape NearCubicWires.Admission
noncomputable section

/-! ## 1. The reserve and the two cycle classes -/

/-- **The reserve** `Rc = C·tableClass L hR q`: coefficient and exponent per `(sources, γ, p)`, fixed before `L`. -/
structure RcChoice where
  C : ParNat
  hR : ParNat

/-- **The refill class family**: 96 reserves (`refill3_fuel_eq`) on the `Rc`-free class `y` (`+115` on its polynomial coefficient). -/
def refFam (R : RcChoice) (y : ClsFam) : ClsFam where
  dP := y.dP
  hT := fun s g hg hh p => max (R.hR s g hg hh p) (y.hT s g hg hh p)
  hS := y.hS
  cP := fun s g hg hh p k => y.cP s g hg hh p k + 115
  cT := fun s g hg hh p k => 96 * R.C s g hg hh p + y.cT s g hg hh p k
  cS := y.cS

/-- **The first-cycle class family**: 102 reserves (`first3_fuel_eq`) on the `Rc`-free class `yF` (`+147`). -/
def firstFam (R : RcChoice) (yF : ClsFam) : ClsFam where
  dP := yF.dP
  hT := fun s g hg hh p => max (R.hR s g hg hh p) (yF.hT s g hg hh p)
  hS := yF.hS
  cP := fun s g hg hh p k => yF.cP s g hg hh p k + 147
  cT := fun s g hg hh p k => 102 * R.C s g hg hh p + yF.cT s g hg hh p k
  cS := yF.cS

abbrev famSite (printer : EightSources → WilliamsAlgorithm) (cVc hV : ParNat) : ClsFam :=
  famFam printer cVc hV (fun _ _ _ _ _ => 22)

def siteRc (printer : EightSources → WilliamsAlgorithm) (cVc hV : ParNat) (y yF : ClsFam) : RcChoice where
  C := fun _ _ _ _ _ => 1
  hR := fun s g hg hh p => max (max ((famSite printer cVc hV).hT s g hg hh p) (y.hT s g hg hh p))
    (max (yF.hT s g hg hh p) (hV s g hg hh p)) + 2

section site

end site

/-! ## 2. Per call: S's two cost premises, EXACTLY -/

section seam

end seam

/-! ## 3. The two `Rc`-free class facts, one fact per owner -/

section owners

end owners

end
end NearCubicWires.SourceBudget
end

