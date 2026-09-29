import Proof.Hierarchy.CompetitorGcdUpdate

/-! One fixed ordinary gcd loop, with no supplied iteration counter. Each
nonterminal pass decreases a+b; the cap on the complete guessed witness
therefore pays for even the largest malformed rational fields. -/
namespace NearCubicWires.RepairOrdinary.CompetitorGcd
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 7→ℕ := ![9,9,9,13,13,6,6]
noncomputable def programs : (j : Fin 7)→Machine 7 (sizes j)
  | ⟨0,_⟩=>check 0
  | ⟨1,_⟩=>check 1
  | ⟨2,_⟩=>check 2
  | ⟨3,_⟩=>update 0
  | ⟨4,_⟩=>update 1
  | ⟨5,_⟩=>select 0
  | ⟨6,_⟩=>select 1
  | ⟨n+7,h⟩=>False.elim (by omega)
def next (j : Fin 7) (_ : Fin (sizes j)) (cells : Fin 7→Bool) : Option (Fin 7) :=
  ![some (if cells 4 then 6 else 1),some (if cells 4 then 5 else 2),
    some (if cells 4 then 4 else 3),some 0,some 0,none,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.CompetitorGcd
