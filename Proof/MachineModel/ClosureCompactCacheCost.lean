import Proof.MachineModel.ClosureRadix

/-! Bytes in the replicated cache are bounded by its occurrence count and
the ORIGINAL per-equation bit bound. Replication is a preparation factor;
it is not used as the radix of a printed equation. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactCacheCost
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierPrime
open RepairSource.CloseoutFinal C10SupplierRowInput
open scoped BigOperators

theorem bit_bound (z : Int) (b : Nat) (hb : 0<b) (hz : z.natAbs < 2^b) :
    intBitLength z ≤ b := by
  have := Nat.log_lt_of_lt_pow' (by omega : b≠0) hz
  unfold intBitLength
  omega

end NearCubicWires.P1Closure.CompactCacheCost
