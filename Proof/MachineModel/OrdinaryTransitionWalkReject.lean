import Proof.MachineModel.OrdinaryTransitionWalkRound

/-! Bounded rejecting branches. Truncated claim checks may leave their local
heads unrestored; the enclosing controller halts after writing false and does
not invoke lookup or reuse those failed fields. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reject_tail (d : Store) :
    ∃ time≤2,Timed machine time (cfg (RecoveryCalls.code sizes 11 (programs 11).start) d)
      (cfg (RecoveryCalls.controlCode sizes none) {d with countFlag:=false}) := by
  obtain ⟨r,hr,hf,_⟩ := clear_run d
  exact stop_phase 11 d {d with countFlag:=false} 1 r hr hf rfl

end NearCubicWires.RepairOrdinary.TransitionWalk
