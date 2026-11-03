import Proof.CaseAnalysis.RowsEstimatorSubstitutionDock

/-! A shared physical delimiter loop serves both factors and monomials. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionRepeat
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle (t : ℕ) : Machine t 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes (s : ℕ) : Fin 2 → ℕ:=![1,s]
def programs {t s : ℕ} (p : Machine t s) : (i : Fin 2) → Machine t (sizes s i)
  | ⟨0,_⟩=>idle t
  | ⟨1,_⟩=>p
  | ⟨n+2,h⟩=>False.elim (by omega)
def next {t s : ℕ} (port : Fin t) (i : Fin 2) (_ : Fin (sizes s i)) (bits : Fin t → Bool) : Option (Fin 2):=
  if i=0 then if bits port then some 1 else none else some 0
noncomputable def machine {t s : ℕ} (p : Machine t s) (port : Fin t):=RecoveryCalls.machine (sizes s) (programs p) 0 (next port)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionRepeat
