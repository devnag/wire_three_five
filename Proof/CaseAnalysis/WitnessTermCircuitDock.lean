import Proof.CaseAnalysis.WitnessTermCircuitReset

/-! The circuit reader directly aliases the retained term payload and
shared internal driver. Every other term/mass field remains outside its
bank; the supplied receipt is the actual circuit call, not a new parser. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCircuitDock
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 1703) : Fin 2532 :=
  ⟨if i.val=1 then 78 else if i.val=1694 then 720 else 827+i.val,by split_ifs <;> omega⟩

theorem slots_injective : Function.Injective slots := by
  intro i j h
  have hv := congrArg (fun k : Fin 2532=>k.val) h
  dsimp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem term_away (i : Fin 827) (hi : i.val≠78 ∧ i.val≠720) :
    ∀ j,slots j≠i.castAdd 1705 := by
  intro j h
  have hv := congrArg (fun k : Fin 2532=>k.val) h
  dsimp only [slots,Fin.val_castAdd] at hv
  split_ifs at hv <;> omega

theorem reset_away (i : Fin 2) : ∀ j,slots j≠i.natAdd 2530 := by
  intro j h
  have hv := congrArg (fun k : Fin 2532=>k.val) h
  dsimp only [slots,Fin.val_natAdd] at hv
  split_ifs at hv <;> omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCircuitDock
