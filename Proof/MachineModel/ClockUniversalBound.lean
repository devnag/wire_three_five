import Proof.MachineModel.ClockBoundGuard

/-! Literal fixed-U bound-field consumer. Canonical B is rejected exactly
when B exceeds the generated dyadic cap, including the overwidth case. -/
namespace NearCubicWires.RepairOrdinary.ClockUniversalBound
open LocalBitMultitape SignedSortKey RadixSemantics ClockDyadicLedger
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def limitWord (N : ℕ) : List Bool := List.replicate (exponent N) false++[true]
@[simp] theorem limitWord_value (N : ℕ) : value (limitWord N)=limit N := by
  simp [limitWord,value_append,value,limit]
theorem limitWord_fits (N : ℕ) : (limitWord N).length≤width N := by
  simp [limitWord,width]
theorem boundWord_fits (N B : ℕ) (hB : B≤limit N) : (ClockBinary.word B).length≤width N := by
  have hwidth := (width_bounds N).1
  exact ClockBinary.length_bound B (width N) (by omega)

end NearCubicWires.RepairOrdinary.ClockUniversalBound
