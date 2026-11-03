import Proof.Packets.BudgetSiteAbsorb

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.RuntimeShape NearCubicWires.Admission
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal

theorem hfamH_sat (sources : EightSources) (k : ℕ) (c : CostCls) (m L hX cX : ℕ) (hm : 2 ≤ m) (hk : c.dP + 1 ≤ k + 2) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ head fuel : ℕ,
      c.In m L n (C10PartsSchedule.widthAt sources k n) fuel →
      head ≤ cX * tableClass L hX (C10PartsSchedule.widthAt sources k n) →
      ∀ C hR : ℕ, 1 ≤ C → c.hT + 2 ≤ hR → hX + 2 ≤ hR →
        head + fuel + 1 ≤ C * tableClass L hR (C10PartsSchedule.widthAt sources k n) := by
  obtain ⟨n0, h0⟩ := class_fuel_lt_Rc sources k c m L hX cX hm hk
  exact ⟨n0, fun n hn head fuel hf hx C hR hC hTR hXR => h0 n hn fuel head hf hx C hR hC hTR hXR⟩

end NearCubicWires.SourceBudget

