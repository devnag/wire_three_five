import Proof.Rows.RowsPoolMinimumPaper

namespace NearCubicWires.RepairSource.CloseoutRowsPoolWriter
open SupplierPipeline RepairRepresentation ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.CloseoutRowsCircuitBottom
open RepairSource.CloseoutRowsUniversal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {q : ℕ}

/-! ### The per-occurrence emission -/

/-- What the writer emits for one retained occurrence: the original request
word, then the frozen request word, each in the batch's own frame. -/
def entry (live : Finset (Fin q)) (g : SupportedNormalizedGate q) : List Bool :=
  frame (nativeWord g)++frame (nativeWord (constantSupportedGate live g))

/-- The original half is the unpooled batch's word, unchanged. -/
theorem original_native (g : SupportedNormalizedGate q) :
    nativeWord g=
      natWord q++(List.ofFn g.gate.weight).flatMap intWord++intWord (g.gate.threshold-1):=rfl

/-- THE WRITER'S FROZEN HALF: original arity header, the X/C weight loop's
own output stream, and the paper's transformed strict threshold. -/
theorem constant_native (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    nativeWord (constantSupportedGate live g)=
      natWord q++
        CloseoutRowsPoolWeight.emitted (CloseoutRowsPoolMinimum.items g.gate live)++
        intWord (g.gate.threshold-minimumLiveScore g.gate live-1):=by
  rw [CloseoutRowsPoolMinimum.items_emitted]
  rfl

/-! ### The pool word -/

theorem pool_cons (live : Finset (Fin q)) (g : SupportedNormalizedGate q)
    (occ : List (SupportedNormalizedGate q)) :
    pool live (g::occ)=g::constantSupportedGate live g::pool live occ:=rfl

/-- The batch's gate stream over the pool is the writer's per-occurrence
emission, in occurrence order. -/
theorem pool_flat (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) :
    (pool live occ).flatMap (fun g=>frame (nativeWord g))=occ.flatMap (entry live):=by
  induction occ with
  | nil=>rfl
  | cons g rest ih=>
    simp only [pool_cons,List.flatMap_cons,entry,ih,List.append_assoc]

/-- ACCEPTANCE: the writer's output stream is byte-equal to the ordered
decomposition-source batch's own segment of the interleaved X/C pool. -/
theorem pool_segment (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (top : List Bool) :
    ExtDecompositionBatch.segment (pool live occ) top=
      natWord (2*occ.length)++frame top++occ.flatMap (entry live):=by
  simp only [ExtDecompositionBatch.segment,pool_length,pool_flat]

/-! ### The pool is one batch, addressed by the existing absolute indices -/


end
end NearCubicWires.RepairSource.CloseoutRowsPoolWriter
