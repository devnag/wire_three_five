import Proof.Amplification.RecoveryAllCodeLayout

/-! One added public stream lifts an existing physical tape injection.
Old aliases are unchanged in value, and the new tape has its own alias. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SupportDock
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {m t : ℕ} (old : Fin m→Fin t) : Fin (m+1)→Fin (t+1):=
  Fin.addCases (m:=m) (n:=1) (fun i=>(old i).castAdd 1) (fun i=>i.natAdd t)


end NearCubicWires.RepairOrdinary.CloseoutWitness.SupportDock
