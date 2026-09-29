import Proof.Circuits.DecompositionCachedChildPosition

/-! The cursor of the paid native-cache scan points at exactly the selected
child, and its cost is bounded by the retained cache and actual arity/count. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCachedChild
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem selected_word {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length) :
    exactListWord gs=(natWord gs.length++(gs.take i).flatMap exactWord)++
      exactWord gs[i]++(gs.drop (i+1)).flatMap exactWord := by
  have hs : gs.take i++gs[i]::gs.drop (i+1)=gs := by
    rw [←List.drop_eq_getElem_cons hi]
    exact List.take_append_drop i gs
  have h := congrArg (fun xs : List (ExactThresholdGate n) =>
    natWord gs.length++xs.flatMap exactWord) hs
  simpa only [List.flatMap_append,List.flatMap_cons,List.append_assoc,exactListWord] using h.symm

end NearCubicWires.RepairOrdinary.DecompositionCachedChild
