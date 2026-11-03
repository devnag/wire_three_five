import Proof.Packets.BudgetReaderCaps
import Proof.CaseAnalysis.FinalPartsSchedule

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceSteps
open NearCubicWires NearCubicWires.RuntimeShape NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal

/-- **`4b+5 ≤ Rc` past one onset**, for the record width `b = floor + (q+1)^r` and every reserve `C·tableClass L hR q` with `C ≥ 1`. -/
theorem enc_sat (sources : EightSources) (r L : ℕ) :
    ∃ q0, ∀ q, q0 ≤ q → ∀ C hR : ℕ, 1 ≤ C →
      4*(C10PartsSchedule.thresholdFloor sources + (q+1)^r) + 5 ≤ C * tableClass L hR q := by
  obtain ⟨q0, h0⟩ := SourceBudget.poly_le_Rc (4*C10PartsSchedule.thresholdFloor sources + 9) r L
  refine ⟨q0, fun q hq C hR hC => ?_⟩
  have h := h0 q hq C hR hC
  have h1 : 1 ≤ (q+1)^r := Nat.one_le_pow _ _ (Nat.succ_pos q)
  have h2 : 4*C10PartsSchedule.thresholdFloor sources + 9 ≤
      (4*C10PartsSchedule.thresholdFloor sources + 9)*(q+1)^r := Nat.le_mul_of_pos_right _ h1
  have e : (4*C10PartsSchedule.thresholdFloor sources + 9)*(q+1)^r =
      4*C10PartsSchedule.thresholdFloor sources*(q+1)^r + 9*(q+1)^r := by ring
  have h3 : 4*C10PartsSchedule.thresholdFloor sources ≤ 4*C10PartsSchedule.thresholdFloor sources*(q+1)^r :=
    Nat.le_mul_of_pos_right _ h1
  omega

/-- **The same at the source's record width and width**: `4·entryWidthSchedule sources k r n + 5 ≤ C·tableClass L hR (widthAt sources k n)`
once `widthAt sources k n` is past the onset. -/
theorem enc_sat_at (sources : EightSources) (k r L : ℕ) :
    ∃ q0, ∀ n, q0 ≤ C10PartsSchedule.widthAt sources k n → ∀ C hR : ℕ, 1 ≤ C →
      4*C10PartsSchedule.entryWidthSchedule sources k r n + 5 ≤
        C * tableClass L hR (C10PartsSchedule.widthAt sources k n) := by
  obtain ⟨q0, h0⟩ := enc_sat sources r L
  exact ⟨q0, fun n hn C hR hC => h0 _ hn C hR hC⟩

end NearCubicWires.SourceSteps

