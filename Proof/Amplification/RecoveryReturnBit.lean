import Proof.Amplification.RecoveryAllCodeCanonicalJoin

/-! Converting the checked Boolean cell into actual accepting/rejecting
finite control takes one local transition. Sequential handoff pays another. -/
namespace NearCubicWires.RepairOrdinary.RecoveryReturnBit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def code (bit : Bool) : Fin 3 := if bit then 1 else 2

def accepting (s : Nat) : Fin (s+3)→Bool :=
  Fin.addCases (m:=s) (n:=3) (motive:=fun _=>Bool) (fun _=>false) (fun q=>q.val==1)

end NearCubicWires.RepairOrdinary.RecoveryReturnBit
