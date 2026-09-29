import Proof.Supplier.RowCachedCoordinateReusable

/-! Uniform scratch capacities for the actual cached-coordinate call. Bounds
come from its native source bytes, so every selected child uses one bank. -/
namespace NearCubicWires.RepairOrdinary.RowCachedCoordinateBounds
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def size {n : ℕ} (gs : List (ExactThresholdGate n)) (w : ℕ) :=
  (exactListWord gs).length+(n+1)*(gs.length+1)+w+1
def inner (w : ℕ) := 32*(w+1)
def outer {n : ℕ} (gs : List (ExactThresholdGate n)) (w : ℕ) := 256*size gs w
def width {n : ℕ} (gs : List (ExactThresholdGate n)) := (exactListWord gs).length+1

theorem child_bytes {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length) :
    (exactWord gs[i]).length≤(exactListWord gs).length := by
  have h := congrArg List.length (DecompositionCachedChild.selected_word gs i hi)
  simp only [List.length_append] at h
  omega

end NearCubicWires.RepairOrdinary.RowCachedCoordinateBounds
