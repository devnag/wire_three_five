import Proof.Supplier.RowPowerNativeEndpoint

/-! The appended P/N blocks denote signed radix digits, including the native
zero convention. Concatenation computes the integer Horner stack directly. -/
namespace NearCubicWires.RepairOrdinary.RowPowerNativeReusable
open LocalBitMultitape RepairRepresentation SignedSortKey RadixSemantics
open Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_resize (w : ℕ) (z : ℤ) (hw : natBitLength z.natAbs≤w) :
    ClockNormalize.resize w (binary (natBitLength z.natAbs) z.natAbs)=binary w z.natAbs := by
  rw [ClockScalarFields.resize_binary w _ (by simpa using hw)]
  rw [binary_value (natBitLength z.natAbs) z.natAbs (Nat.lt_pow_succ_log_self (by decide) _)]

theorem digits_same (sign : Bool) (bits : List Bool) : RowPowerBlock.digits sign sign bits=bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simpa [RowPowerBlock.digits,RowPowerBlock.part] using congrArg (List.cons b) ih
theorem digits_other (a b : Bool) (bits : List Bool) (hab : a≠b) :
    RowPowerBlock.digits a b bits=List.replicate bits.length false := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    cases a <;> cases b <;> simp_all [RowPowerBlock.digits,RowPowerBlock.part,List.replicate_succ]

theorem block_binary (w : ℕ) (z : ℤ) (hw : natBitLength z.natAbs≤w) :
    block w z false=binary w z.toNat ∧ block w z true=binary w (-z).toNat := by
  unfold block
  rw [native_resize w z hw]
  cases z with
  | ofNat n =>
    have hs : decide ((Int.ofNat n)<0)=false := by simp
    rw [hs,digits_same,digits_other true false _ (by decide),binary_length]
    simp [RankCarrier.binary_zero]
  | negSucc n =>
    simp only [Int.negSucc_lt_zero,decide_true,Int.natAbs_negSucc,Int.toNat_negSucc,
      Int.neg_negSucc,Int.toNat_natCast,digits_same]
    rw [digits_other false true _ (by decide),binary_length,RankCarrier.binary_zero]
    trivial


end NearCubicWires.RepairOrdinary.RowPowerNativeReusable
