import Proof.SourceAssembly.AdmissionCaps

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.P1Closure

noncomputable section

/-- The uniform degree at arity `q` and live scale `L`. -/
def uniformDeg (q L : ℕ) : ℕ := q/(200*(normalizedLiveCount q L + 2))

section
variable {a : DecompositionAlgorithm} {q L : ℕ} {F : Packets.Family q L} {g : Packets.Geometry F}

/-- Every row degree of a family is below the width of any of its layouts. -/
theorem row_degree_lt_w (layout : Packets.Layout a F g) :
    ∀ row ∈ F.rows, row.degree < layout.w := by
  intro row hrow
  have h := layout.widthFromTouch g.touch row hrow
  have h2 : 2 ≤ Packets.alphabet a F := by unfold Packets.alphabet; omega
  have hp : 2^row.degree ≤ (Packets.alphabet a F)^row.degree := Nat.pow_le_pow_left h2 _
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp (hp.trans_lt h)

/-- The width of any layout is at most the uniform degree. -/
theorem w_le_uniformDeg (layout : Packets.Layout a F g) : layout.w ≤ uniformDeg q L := by
  have hl := layout.load
  unfold Packets.residual at hl
  unfold uniformDeg
  rw [Nat.le_div_iff_mul_le (by positivity)]
  have : 200*(normalizedLiveCount q L + layout.w*(normalizedLiveCount q L+2)) =
      200*normalizedLiveCount q L + layout.w*(200*(normalizedLiveCount q L+2)) := by ring
  omega


end


end
end NearCubicWires.Admission
