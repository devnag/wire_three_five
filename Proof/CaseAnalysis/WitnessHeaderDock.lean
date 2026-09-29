import Proof.CaseAnalysis.WitnessInput

/-! A cold family directly aliases the bounded header's three payload
ports and one fresh shared verdict. Its remaining tapes occupy its own
fresh segment, so the two mode branches require no input copying. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.HeaderDock
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (m : ℕ):=150+(m+1)
def old (m : ℕ) (i : Fin 150) : Fin (tapes m):=i.castAdd (m+1)
def flag (m : ℕ) : Fin (tapes m):=(0 : Fin (m+1)).natAdd 150

def slots {t : ℕ} (m offset O F V : ℕ) (h:offset+t ≤ m) (i : Fin t) : Fin (tapes m):=
  if i.val=F then old m 118 else if i.val=O then old m 78
  else if i.val=2 then old m 0 else if i.val=V then flag m
  else (⟨1+offset+i.val,by have hi:=i.isLt;omega⟩ : Fin (m+1)).natAdd 150

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.HeaderDock
