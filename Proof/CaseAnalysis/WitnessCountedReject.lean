import Proof.Amplification.RecoveryRepeatRejectedTape

/-! The existing rejecting repeater needs a body receipt only at the
actual guarded indices. No body runs at the exhausted end of the stream. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CountedReject
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
open private successful_cfg_eq from Proof.PCP.VerifierDecodingRejectingRepeat

def advance {α : Type} (next : ℕ → α → Bool×α) (x : ℕ×α) : Bool×(ℕ×α) :=
  ((next x.1 x.2).1,(x.1+1,(next x.1 x.2).2))

end NearCubicWires.RepairOrdinary.CloseoutWitness.CountedReject
