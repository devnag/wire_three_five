import Proof.SourceAssembly.SourceRefillSeam3
import Proof.Packets.BudgetSeamWindows
import Proof.Packets.BudgetCycFuel

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section seam

end seam

/-- **`windows_of_free`'s premise is satisfiable** (class form): if `restCost|₀ + cycFuel 0` lies in class `y` at
`q = widthAt sources k n`, then `restCost|₀ + cycFuel 0 + 2 ≤ Rc = C·tableClass L hR q` past an onset chosen after `L`, for every
`C ≥ 1`, once `hR ≥ y.hT + 2` and `y.dP + 1 ≤ k + 2`. With S's `windows_of_free` this gives `hwinI` and `hwinZ` at `Rk = 16(Rc+1)`. -/
theorem windows3_sat (sources : EightSources) (k : ℕ) (y : CostCls) (m L : ℕ) (hm : 2 ≤ m) (hk : y.dP + 1 ≤ k + 2) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ free : ℕ, y.In m L n (C10PartsSchedule.widthAt sources k n) free →
      ∀ C hR : ℕ, 1 ≤ C → y.hT + 2 ≤ hR →
        free + 2 ≤ C * tableClass L hR (C10PartsSchedule.widthAt sources k n) := by
  obtain ⟨n0, h0⟩ := class_fuel_lt_Rc sources k y m L 0 1 hm hk
  refine ⟨n0, fun n hn free hf C hR hC hTR => ?_⟩
  have h1 : 1 ≤ 1 * tableClass L 0 (C10PartsSchedule.widthAt sources k n) := by
    rw [one_mul]; exact SourceConstruction.one_le_tableClass _ _ _
  have h := h0 n hn free 1 hf h1 C hR hC hTR (by omega)
  omega

end
end NearCubicWires.SourceBudget
end

