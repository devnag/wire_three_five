import Proof.Packets.BudgetTableOnset
import Proof.Packets.BudgetCycleClass

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.RuntimeShape NearCubicWires.Admission NearCubicWires.P1Closure
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SupplierEstimator NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

/-- **A `V`-linear quantity fits the reserve** past an onset chosen after `L`, for every `C ≥ 1`, once `hR ≥ hV + 2`. -/
theorem Vlin_le_Rc (sources : EightSources) (k L c d cVc hV : ℕ) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ C hR : ℕ, 1 ≤ C → hV + 2 ≤ hR →
      c * (cVc * tableClass L hV (C10PartsSchedule.widthAt sources k n)) + d + 1 ≤
        C * tableClass L hR (C10PartsSchedule.widthAt sources k n) := by
  obtain ⟨n0, h0⟩ := split_add_lt_Rc sources k 0 hV 0 2 L d (c*cVc) 0 0 0 le_rfl (by omega)
  refine ⟨n0, fun n hn C hR hC hVR => ?_⟩
  have h := h0 n hn 0 (Nat.zero_le _) C hR hC hVR (by omega)
  unfold splitRHS at h
  simp only [pow_zero, mul_one, zero_mul, add_zero] at h
  have e : c * (cVc * tableClass L hV (C10PartsSchedule.widthAt sources k n)) =
      c*cVc * ((C10PartsSchedule.widthAt sources k n + 1)^hV *
        2^(C10PartsSchedule.widthAt sources k n - normalizedLiveCount (C10PartsSchedule.widthAt sources k n) L)) := by
    unfold tableClass; ring
  rw [e]
  omega

/-- **S's four reserve premises at `V = cVc·tableClass L hV q`** (`hSl`, `hRl`, `hBl`, `hdescR` with `descriptorReserve := V`):
all hold past ONE onset after `L`, for every `C ≥ 1`, once `hR ≥ hV + 2`. -/
theorem reserves_le_Rc (printer : WilliamsAlgorithm) (sources : EightSources) (k L cVc hV : ℕ) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ C hR : ℕ, 1 ≤ C → hV + 2 ≤ hR →
      P1TopDownPaidReusableReserves.workspace printer (cVc * tableClass L hV (C10PartsSchedule.widthAt sources k n)) + 2 ≤
          C * tableClass L hR (C10PartsSchedule.widthAt sources k n) ∧
      P1TopDownPaidReusableReserves.rewind printer (cVc * tableClass L hV (C10PartsSchedule.widthAt sources k n)) + 2 ≤
          C * tableClass L hR (C10PartsSchedule.widthAt sources k n) ∧
      P1TopDownPaidReusableReserves.buffer (cVc * tableClass L hV (C10PartsSchedule.widthAt sources k n)) + 2 ≤
          C * tableClass L hR (C10PartsSchedule.widthAt sources k n) ∧
      cVc * tableClass L hV (C10PartsSchedule.widthAt sources k n) ≤
          C * tableClass L hR (C10PartsSchedule.widthAt sources k n) := by
  set c := 2*P1TopDownPaidReusableReserves.coefficient printer + 20 with hc
  obtain ⟨n0, h0⟩ := Vlin_le_Rc sources k L c (c + 2) cVc hV
  refine ⟨n0, fun n hn C hR hC hVR => ?_⟩
  have h := h0 n hn C hR hC hVR
  set V := cVc * tableClass L hV (C10PartsSchedule.widthAt sources k n) with hVd
  have hW : P1TopDownPaidReusableReserves.workspace printer V = c*(V+1) := by
    unfold P1TopDownPaidReusableReserves.workspace; rw [hc]
  have hRw : P1TopDownPaidReusableReserves.rewind printer V ≤ c*(V+1) := by
    unfold P1TopDownPaidReusableReserves.rewind
    exact Nat.mul_le_mul_right _ (by omega)
  have hB : P1TopDownPaidReusableReserves.buffer V = V + 1 := rfl
  have hcV : V ≤ c*V := Nat.le_mul_of_pos_left _ (by omega)
  have e : c*(V+1) = c*V + c := by ring
  refine ⟨by omega, by omega, by omega, by omega⟩

end NearCubicWires.SourceBudget

