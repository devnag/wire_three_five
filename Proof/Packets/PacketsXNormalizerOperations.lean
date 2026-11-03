import Mathlib.Data.List.OfFn
import Proof.Packets.NormalizerOrder
import Proof.Packets.PacketsXNormalizedRing
import Proof.Packets.PhysicalCoefficientAlgebra

/-! Exact ordered raw inputs for each normalized arithmetic primitive. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizerOrder
open PhysicalCoefficientAlgebra
variable {α : Type}

/-- Cartesian support unions are normalized in the compiler's literal
left-major, right-minor traversal order. -/
theorem mul_raw [LinearOrder α] (P Q : Ring.Poly α) :
    Ring.norm (P.flatMap (fun m=>Q.map (fun n=>m++n)))=Ring.mul P Q := by
  simp only [Ring.norm,List.foldl_flatMap,List.foldl_map,Ring.mul]

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizerOrder
