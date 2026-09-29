import Proof.Assembly.RowsPoolWeightArms

/-! The live mask physically selects copy versus literal zero. Both arms
consume the original native integer and leave one shared reusable width
scratch. The coordinate loop uses the retained mask cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
open LocalBitMultitape RecoveryRootRound RecoveryExecution ExtDecompositionBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def probe : Machine 4 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes : Fin 3→ℕ:=![1,6,11]
noncomputable def programs : (j : Fin 3)→Machine 4 (sizes j)
  | ⟨0,_⟩=>probe
  | ⟨1,_⟩=>copy
  | ⟨2,_⟩=>replaced
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 4→Bool) : Option (Fin 3):=
  if j=0 then some (if bits 3 then 2 else 1) else none
noncomputable def choice:=RecoveryCalls.machine sizes programs 0 next

theorem probe_run (H : Fin 4→ℕ) (A : Fin 4→List Bool) :
    Step probe 0 H A H A:=by
  obtain ⟨r,hr,hf,_⟩:=(Timed.refl probe (⟨0,H,A⟩ : Configuration 4 1)).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)


end NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
