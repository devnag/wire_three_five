import Proof.Supplier.RowOccurrenceLoop
import Proof.Supplier.RowPowerBinLift

/-! The executed occurrence-coordinate loop assembles the power-radix stack
of actual native child equations. The radix is safe by their native bytes;
only the conjunction is identified with the canonical equation stack. -/
namespace NearCubicWires.RepairOrdinary.RowCachedEquation
open LocalBitMultitape RepairRepresentation SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
open RowOccurrenceLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def equation {n : ℕ} (g : ExactThresholdGate n) : LabelledEquation (Fin n) := ⟨g.weight,g.target⟩
def equations {n : ℕ} (gs : List (ExactThresholdGate n)) (indices : List (Fin gs.length)) :=
  indices.map (fun i=>equation gs[i.val])

theorem native_abs_sum (zs : List ℤ) :
    (zs.map Int.natAbs).sum<2^(zs.flatMap intWord).length := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hk : natBitLength z.natAbs≤(intWord z).length := by
      simp only [DecompositionSource.intWord_length,intBitLength,natBitLength]
      omega
    have hz : z.natAbs<2^(intWord z).length :=
      (Nat.lt_pow_succ_log_self (by decide : 1<2) z.natAbs).trans_le
        (Nat.pow_le_pow_right (by decide) hk)
    have hp := Nat.mul_le_mul (Nat.succ_le_of_lt hz) (Nat.succ_le_of_lt ih)
    simp only [Nat.succ_eq_add_one] at hp
    have hn : 0≤z.natAbs*(zs.map Int.natAbs).sum := Nat.zero_le _
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,pow_add]
    nlinarith

theorem equation_magnitude {n : ℕ} (g : ExactThresholdGate n) :
    equationMagnitudeBound (equation g)<2^(exactWord g).length := by
  have h := native_abs_sum (RowNativeCoordinate.fields g)
  rw [←RowNativeCoordinate.word_fields] at h
  simpa [equationMagnitudeBound,equation,RowNativeCoordinate.fields,List.map_ofFn,List.sum_ofFn] using h

theorem cache_radix_safe {n : ℕ} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) :
    equationMagnitudeBound (equation gs[i.val])<2^(RowCachedCoordinateBounds.width gs) := by
  apply (equation_magnitude gs[i.val]).trans_le
  apply Nat.pow_le_pow_right (by decide)
  exact (RowCachedCoordinateBounds.child_bytes gs i.val i.isLt).trans (Nat.le_succ _)

end NearCubicWires.RepairOrdinary.RowCachedEquation
