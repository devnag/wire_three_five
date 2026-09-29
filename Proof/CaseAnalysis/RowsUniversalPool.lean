import Proof.CaseAnalysis.RawRowsMonomials
import Proof.CaseAnalysis.RowsRawLogShape

/-! Appendix A.2's universal X/C pool for the actual ordinary decomposition.
The interleaved list is independent of the frozen column: both original and
constant gates are submitted to the same physical source batch. -/
namespace NearCubicWires.RepairSource.CloseoutRowsUniversal
open SupplierPipeline RepairRepresentation ThresholdCompiler
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {q : ℕ}

def constantSupportedGate (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    SupportedNormalizedGate q where
  gate:={
    weight:=fun i=>if i∈live then 0 else g.gate.weight i
    threshold:=g.gate.threshold-minimumLiveScore g.gate live}
  support:=g.support\live
  zeroOutside:=by
    intro i hi
    change (if i∈live then 0 else g.gate.weight i)=0
    by_cases h:i∈live
    · exact if_pos h
    · rw [if_neg h]
      exact g.zeroOutside i (by intro hg; exact hi (Finset.mem_sdiff.mpr ⟨hg,h⟩))

@[simp] theorem constant_weight (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (i : Fin q) :
    (constantSupportedGate live g).gate.weight i=if i∈live then 0 else g.gate.weight i:=rfl
@[simp] theorem constant_threshold (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    (constantSupportedGate live g).gate.threshold=g.gate.threshold-minimumLiveScore g.gate live:=rfl

def pool (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) :=
  occ.flatMap (fun g=>[g,constantSupportedGate live g])

@[simp] theorem pool_length (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) :
    (pool live occ).length=2*occ.length:=by
  induction occ with
  | nil=>rfl
  | cons g occ ih=>simp only [pool,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *; omega

end
end NearCubicWires.RepairSource.CloseoutRowsUniversal
