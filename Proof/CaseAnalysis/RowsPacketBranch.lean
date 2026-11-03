import Proof.CaseAnalysis.RowsPacketFlag

/-! The fixed packet branch consumes one marker, skips an absent polynomial,
or executes the enclosing positive polynomial program. Every return is paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes (s : ℕ) : Fin 2→ℕ := ![3,s]
def programs {t s : ℕ} (source : Fin t) (body : Machine t s) :
    (j : Fin 2)→Machine t (sizes s j)
  | ⟨0,_⟩=>CloseoutRowsPacketFlag.machine source
  | ⟨1,_⟩=>body
  | ⟨j+2,hj⟩=>False.elim (by omega)
def next {t s : ℕ} (j : Fin 2) (q : Fin (sizes s j)) (_ : Fin t→Bool) : Option (Fin 2) :=
  if j.val=0 ∧ q.val=1 then some 1 else none
noncomputable def machine {t s : ℕ} (source : Fin t) (body : Machine t s) :=
  RecoveryCalls.machine (sizes s) (programs source body) 0 next

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketBranch
