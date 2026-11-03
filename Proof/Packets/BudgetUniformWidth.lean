import Proof.SourceAssembly.AdmissionLayout

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.SupplierEstimator NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open PCJ9eff70d512234a4c_Fixed

noncomputable section

/-- **The uniform packet width**: the largest `w` with `200·(K + w·(K+2)) ≤ q - K`, `K = normalizedLiveCount q L`. -/
def wU (q L : ℕ) : ℕ :=
  ((q - normalizedLiveCount q L) / 200 - normalizedLiveCount q L) / (normalizedLiveCount q L + 2)

/-- The load arithmetic: any `w` meeting the load is `≤ wU`, and `wU` meets the load whenever some `w` does. -/
theorem load_iff_le_wU (q L w : ℕ) (h : 200*(normalizedLiveCount q L + w*(normalizedLiveCount q L + 2)) ≤
    q - normalizedLiveCount q L) :
    w ≤ wU q L ∧ 200*(normalizedLiveCount q L + wU q L*(normalizedLiveCount q L + 2)) ≤ q - normalizedLiveCount q L := by
  unfold wU
  generalize normalizedLiveCount q L = K at h ⊢
  generalize q - K = R at h ⊢
  have hR : K + w*(K+2) ≤ R/200 := by
    rw [Nat.le_div_iff_mul_le (by decide)]; omega
  have hw : w*(K+2) ≤ R/200 - K := by omega
  have h1 : w ≤ (R/200 - K)/(K+2) := by
    rw [Nat.le_div_iff_mul_le (by omega)]; exact hw
  refine ⟨h1, ?_⟩
  have h2 : (R/200 - K)/(K+2)*(K+2) ≤ R/200 - K := Nat.div_mul_le_self _ _
  have h3 : 200*(R/200) ≤ R := Nat.mul_div_le R 200
  omega

variable {q L : ℕ} {a : DecompositionAlgorithm} {F : Packets.Family q L} {g : Packets.Geometry F}

/-- Every layout's width is below the uniform width. -/
theorem w_le_wU (ℓ : Packets.Layout a F g) : ℓ.w ≤ wU q L :=
  (load_iff_le_wU q L ℓ.w ℓ.load).1


end
end NearCubicWires.SourceBudget

