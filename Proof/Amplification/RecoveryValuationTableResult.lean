import Proof.Amplification.RecoveryCertificateCountWitness

/-! The bounded physical table scanner returns the exact shared finite
valuation value, with rejection characterized on every serialized suffix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationTable
open LocalBitMultitape RecoveryValuationStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem reject_ne_success (s : Nat) : RepeatMachine.phaseCode s 4≠RepeatMachine.phaseCode s 3 := by
  intro h
  have he := (RepeatMachine.code s).injective h
  cases he

theorem result_acceptance (total : Nat) (x : Cursor)
    (final : Configuration 9 (Fintype.card (RepeatMachine.Control (Fintype.card (RecoveryCalls.Control sizes)))))
    (h : RepeatMachine.Result source total (RepeatMachine.iterate next total x) final) :
    final.control=RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control sizes)) 3 ↔
      (readMany (readEntry x.data.width) total x.rest).isSome=true := by
  rw [←iterate_accepts]
  cases ha : (RepeatMachine.iterate next total x).1 with
  | false =>
    simp only [RepeatMachine.Result,ha,Bool.false_eq_true,↓reduceIte] at h
    rw [h]
    simp only [Bool.false_eq_true,iff_false]
    exact reject_ne_success _
  | true =>
    simp only [RepeatMachine.Result,ha,↓reduceIte] at h
    rw [h]
    exact iff_of_true rfl rfl

end NearCubicWires.RepairOrdinary.RecoveryValuationTable
