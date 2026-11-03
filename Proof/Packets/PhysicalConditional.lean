import Proof.Amplification.RecoveryCursorCalls

/-! Execute a fixed continuation exactly when the first machine's actual
terminal control accepts. Both return transitions are paid. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.PhysicalConditional
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound

def sizes (a b : Nat) : Fin 2 → Nat := ![a,b]
def programs {t a b : Nat} (p : Machine t a) (q : Machine t b) :
    (j : Fin 2) → Machine t (sizes a b j)
  | 0 => p
  | 1 => q
def next {t a b : Nat} (accept : Fin a → Bool) :
    (j : Fin 2) → Fin (sizes a b j) → (Fin t → Bool) → Option (Fin 2)
  | 0, state, _ => if accept state then some 1 else none
  | 1, _, _ => none
noncomputable def machine {t a b : Nat} (p : Machine t a) (q : Machine t b) (accept : Fin a → Bool) :=
  RecoveryCalls.machine (sizes a b) (programs p q) 0 (next accept)

end PCJ9eff70d512234a4c_Fixed.PhysicalConditional
