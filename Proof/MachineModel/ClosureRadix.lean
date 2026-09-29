import Proof.MachineModel.ClosureCompactBounds

/-! A.12's per-equation radix and per-monomial degree are independent of
cache cardinality. This is data supplied by the actual retained family;
its sole semantic premise is proved for the actual pool below. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.RepairOrdinary
open RepairRepresentation SupplierPipeline SupplierEstimator ThresholdCompiler SupplierPrime

class P1Radix {n : Nat} (gs : List (ExactThresholdGate n)) where
  bits : Nat
  positive : 0 < bits
  safe : ∀ i : Fin gs.length,
    equationMagnitudeBound (RowCachedEquation.equation gs[i.val]) < 2^bits
  degree : Nat

namespace P1Radix

end P1Radix

noncomputable abbrev p1ActualRadix {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2 = liveᶜ.card) (degree : Nat) :
    P1Radix (RepairSource.CloseoutFinal.C10SupplierRowInput.pool a live occ s harity) where
  bits := P1Closure.CompactBounds.radix a live occ
  positive := by unfold P1Closure.CompactBounds.radix; omega
  safe := fun i => P1Closure.CompactBounds.pool_magnitude a live occ s harity _
    (List.getElem_mem i.isLt)
  degree := degree

end NearCubicWires.RepairOrdinary
