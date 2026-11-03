import Proof.Packets.BudgetTableOnset
import Proof.Packets.BudgetFamilyAt
import Proof.Packets.BudgetSiteOrder

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

/-! ## 1. The recipe's hierarchy index dominates the base class's polynomial exponent -/

/-! ## 2. `Rc > familyCost`: a class's cost plus a head, below the reserve -/

/-- **A cost in class `c` plus a table-class head fits the reserve** `Rc = C·tableClass L hR q` (`q = widthAt sources k n`), for
EVERY `C ≥ 1`, past an onset chosen after `L`, once `hR ≥ c.hT + 2`. At `c := famClsAt …` and `fuel :=` the per-entry family fuel
(`family_hcost_at`), this is S's `hfamH : r_inputH … + fuel' + 1 ≤ Rc`. -/
theorem class_fuel_lt_Rc (sources : EightSources) (k : ℕ) (c : CostCls) (m L hX cX : ℕ) (hm : 2 ≤ m)
    (hk : c.dP + 1 ≤ k + 2) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ fuel x : ℕ,
      c.In m L n (C10PartsSchedule.widthAt sources k n) fuel →
      x ≤ cX * tableClass L hX (C10PartsSchedule.widthAt sources k n) →
      ∀ C hR : ℕ, 1 ≤ C → c.hT + 2 ≤ hR → hX + 2 ≤ hR →
        x + fuel + 1 ≤ C * tableClass L hR (C10PartsSchedule.widthAt sources k n) := by
  obtain ⟨n0, h0⟩ := split_add_lt_Rc sources k c.dP c.hT c.hS m L c.cP c.cT c.cS hX cX hm hk
  refine ⟨n0, fun n hn fuel x hfuel hx C hR hC hTR hXR => ?_⟩
  have h := h0 n hn x hx C hR hC hTR hXR
  have hf : fuel ≤ splitRHS c.dP c.hT c.hS m L c.cP c.cT c.cS n (C10PartsSchedule.widthAt sources k n) := hfuel
  omega

/-! ## 3. `refillCost ≥ 14·Rc` inside the site class -/

/-! ## 4. Both at once, in one base class -/

end
end NearCubicWires.SourceBudget
end

