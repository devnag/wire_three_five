import Proof.Packets.BudgetSiteAbsorb

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

/-! ## 1. Class families -/

/-- **A per-parameter cost class**: exponents per `(sources, γ, p)` (the small exponent may read the live scale, its last
argument), coefficients per hierarchy index `k` (the last argument of `cP cT cS`). -/
structure ClsFam where
  dP : ParNat
  hT : ParNat
  hS : ParCoef
  cP : ParCoef
  cT : ParCoef
  cS : ParCoef

/-- The class at live scale `L` and index `k`. -/
def ClsFam.at (c : ClsFam) (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) (L k : ℕ) : CostCls :=
  ⟨c.dP sources gamma hg hh p, c.hT sources gamma hg hh p, c.hS sources gamma hg hh p L,
    c.cP sources gamma hg hh p k, c.cT sources gamma hg hh p k, c.cS sources gamma hg hh p k⟩

/-- The join (maximal exponents, summed coefficients), parameterwise. -/
def ClsFam.join (c d : ClsFam) : ClsFam where
  dP := fun s g hg hh p => max (c.dP s g hg hh p) (d.dP s g hg hh p)
  hT := fun s g hg hh p => max (c.hT s g hg hh p) (d.hT s g hg hh p)
  hS := fun s g hg hh p L => max (c.hS s g hg hh p L) (d.hS s g hg hh p L)
  cP := fun s g hg hh p k => c.cP s g hg hh p k + d.cP s g hg hh p k
  cT := fun s g hg hh p k => c.cT s g hg hh p k + d.cT s g hg hh p k
  cS := fun s g hg hh p k => c.cS s g hg hh p k + d.cS s g hg hh p k

/-! ## 2. The site's class: family ⊔ refill ⊔ first -/

def siteCls (fam ref first : ClsFam) : ClsFam := (fam.join ref).join first

/-- **The family class family**: `famClsAt` at the schedule exponent `r = rSel`, the printer, `V`'s constants and `Dw`'s
coefficient per `(sources, γ, p)`; exponents taken at `k = 0` (they are `k`-free), coefficients at `k`. -/
def famFam (printer : EightSources → WilliamsAlgorithm) (cVc hV dC : ParNat) : ClsFam where
  dP := fun s g hg hh p => (famClsAt (printer s) s p 0 (rSel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).dP
  hT := fun s g hg hh p => (famClsAt (printer s) s p 0 (rSel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).hT
  hS := fun s g hg hh p _ => (famClsAt (printer s) s p 0 (rSel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).hS
  cP := fun s g hg hh p k => (famClsAt (printer s) s p k (rSel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).cP
  cT := fun s g hg hh p k => (famClsAt (printer s) s p k (rSel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).cT
  cS := fun s g hg hh p k => (famClsAt (printer s) s p k (rSel s p) (cVc s g hg hh p) (hV s g hg hh p) (dC s g hg hh p)).cS

end
end NearCubicWires.SourceBudget
end

