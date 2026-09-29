import Proof.CaseAnalysis.WitnessSupportDock

/-! Static exchange of the last two labels restores the original repeat
counter alias while putting retained support last. No tape movement runs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Exchange
open LocalBitMultitape CloseoutWitness.SupportDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout (t : ℕ) : Fin (t+1+1) ≃ Fin (t+1+1):=
  Equiv.swap ⟨t,by omega⟩ ⟨t+1,by omega⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Exchange
