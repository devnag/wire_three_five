import Proof.MachineModel.Runs
import Proof.PCP.PCPSerializerTapeSupport

/-! Derive allocated output support from a checked execution receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary

theorem Step.tape_length {t s fuel : Nat} {machine : Machine t s}
    {hin hout : Fin t → Nat} {tin tout : Fin t → List Bool}
    (run : Step machine fuel hin tin hout tout) (i : Fin t) (cap position : Nat)
    (hh : hin i ≤ position) (ht : (tin i).length ≤ cap) :
    (tout i).length ≤ max cap (position+fuel+1) := by
  obtain ⟨r,hr,_,he,hfuel⟩:=run
  have h:=PCPSerializerReuse.tape_support machine fuel _ r hr i cap position hh
    (ht.trans (Nat.le_max_left _ _))
  rw [he] at h
  exact h.trans (max_le_max_left _ (by omega))

end NearCubicWires.ExtDecompositionBatch
