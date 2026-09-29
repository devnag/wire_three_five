import Proof.CaseAnalysis.WitnessInputGuard

/-! The actual produced native width is compared to the retained original
input length before oracle parsing. Both raw fields survive the existing
paid comparator, including on the rejecting R>N branch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeGuard
open LocalBitMultitape RecoveryRootRound RepairSource.CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots {t : ℕ} (fields : Fin 2 → Fin t) : Fin 6 → Fin (t+4):=
  Fin.addCases (m:=2) (n:=4) (motive:=fun _=>Fin (t+4)) (fun i=>(fields i).castAdd 4) (Fin.natAdd t)
def machine {t : ℕ} (fields : Fin 2 → Fin t):=RecoveryFocus.machine (slots fields) RawCompare.machine
def flagSlot (t : ℕ):=(2 : Fin 4).natAdd t

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeGuard
