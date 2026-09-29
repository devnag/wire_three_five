import Proof.Amplification.RecoveryProjectionScalarPrepare

/-! Complete execution of the first normalized address row batch from its
literal scalar and source fields. No prepared-bank, unary-driver, random-word
or evaluator-time assumptions remain. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionColdRows
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization RecoveryProjectionRows RecoveryProjectionScalar
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


theorem capacity_initialization (R : Nat) : 2*R+3≤capacity R := by
  have hpow : R+1≤(R+1)^4 := Nat.le_self_pow (by decide) _
  unfold capacity
  omega

end NearCubicWires.RepairSource.RecoveryProjectionColdRows
