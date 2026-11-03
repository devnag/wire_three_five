import Proof.Rows.RowsThrKey

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrSel
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeySucc RowsConstruction.KeyTop
open RowsConstruction.ThrKey
noncomputable section

/-! ## 1. Generic facts about the carry cascade `next` -/

section Generic
variable {ι : Type} [DecidableEq ι]

theorem zero_zero : ∀ (ls : List (Level ι)), zero ls (fun _ => 0) = fun _ => 0
  | [] => rfl
  | l :: ls => by
    simp only [zero]
    have e : Function.update (fun _ : ι => (0 : ℕ)) l.field 0 = fun _ => 0 := by
      funext x; by_cases hx : x = l.field <;> simp [hx]
    rw [e]
    exact zero_zero ls

end Generic

/-! ## 2. The physical four-digit cascade -/

def c4 (c : Fin 4) : Fin 8 := ⟨c.val, by omega⟩

/-! ## 3. The THR request's cascade is `casc` on the padded bounds -/

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- Child digits past the request's circuits are `0` in every key. -/
theorem dig_pad (k : RCFive.RowKeys.ThrKey a r L target) (c : Fin 4) (hc : ¬ c.val < r.circuits.length) :
    dig a r L target k (c4 c) = 0 := by
  unfold dig thrDigitsOf
  rw [dif_neg (by simpa [c4] using hc)]
  have := c.isLt
  have h4 : ¬ (c4 c).val = 4 := by simp [c4]; omega
  have h5 : ¬ (c4 c).val = 5 := by simp [c4]; omega
  have h6 : ¬ (c4 c).val = 6 := by simp [c4]; omega
  rw [if_neg h4, if_neg h5, if_neg h6]

include four in
/-- The key's child digits are the base worker's digits. -/
theorem data_digits (k : RCFive.RowKeys.ThrKey a r L target) (c : Fin 4) :
    (PCJ45bee56da9f34d5a_StreamPair.data a r four k.selection).digits c = dig a r L target k (c4 c) := by
  by_cases hc : c.val < r.circuits.length
  · have e := dig_sel a r four L target k ⟨c.val, hc⟩
    rw [show c4 c = ⟨c.val, by omega⟩ from rfl, e]
    simp [PCJ45bee56da9f34d5a_FourfoldBaseData.Data.digits, PCJ45bee56da9f34d5a_StreamPair.data,
      PCJ45bee56da9f34d5a_ThresholdData.data, hc]
  · rw [dig_pad a r L target k c hc]
    simp [PCJ45bee56da9f34d5a_FourfoldBaseData.Data.digits, PCJ45bee56da9f34d5a_StreamPair.data,
      PCJ45bee56da9f34d5a_ThresholdData.data, hc]

include four in

theorem dig_key0 (h0 : 0 < (KeySucc.keys a r L target).length) :
    dig a r L target (KeySucc.keys a r L target)[0] = fun _ => 0 := by
  have hne : PacketFamilyParent.rcKeys a (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target) ≠ [] := by
    change KeySucc.keys a r L target ≠ []
    intro h
    rw [h] at h0
    simp at h0
  have hh := (enum_next (spec a r four L target) (cursorSpec_wf a _) (cursorSpec_pos a _ hne) (fun _ => 0)).2.2
  rw [← thr_digits a r four L target, zero_zero, List.head?_map, List.head?_eq_getElem?,
    List.getElem?_eq_getElem h0] at hh
  exact Option.some.inj hh

/-! ## 4. The masters of any two keys -/

/-! ## 5. Case Sel at the bank -/

end Thr

end
end RowsConstruction.ThrSel
