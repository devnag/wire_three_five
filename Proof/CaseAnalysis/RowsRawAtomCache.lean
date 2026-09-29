import Proof.CaseAnalysis.RowsRawAtomSeek

/-! The cache reader's polynomial list is exactly the output of the actual
source-count producer. Its indices are absolute positions in the SAME GS;
zero-child occurrences retain a cache slot. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomCache
open CanonicalFourfoldRowProgram ExtDecompositionBatch SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cache : ℕ→List ℕ→List (List (List ℕ))
  | _,[]=>[]
  | offset,n::ns=>CloseoutRowsRawAtomLoop.indices offset n::cache (offset+n) ns

theorem cache_length (offset : ℕ) (ns : List ℕ) : (cache offset ns).length=ns.length := by
  induction ns generalizing offset with
  | nil=>rfl
  | cons n ns ih=>simp [cache,ih]

theorem cache_getElem (offset : ℕ) (ns : List ℕ) (i : ℕ) (hi : i<ns.length) :
    (cache offset ns)[i]'(by rw [cache_length];exact hi)=
      CloseoutRowsRawAtomLoop.indices (offset+(ns.take i).sum) ns[i] := by
  induction ns generalizing offset i with
  | nil=>simp at hi
  | cons n ns ih=>
    cases i with
    | zero=>simp [cache]
    | succ i=>
      have h:i<ns.length:=by simpa using hi
      simpa [cache,List.take_succ_cons,Nat.add_assoc] using ih (offset+n) i h

def sourceCache {q : ℕ} (a : RepairRepresentation.DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)):=cache 0 (counts a occ)

theorem source_length {q : ℕ} (a : RepairRepresentation.DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) : (sourceCache a occ).length=occ.length := by
  simp [sourceCache,cache_length,counts_length]

theorem source_getElem {q : ℕ} (a : RepairRepresentation.DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) (i : ℕ) (hi : i<occ.length) :
    (sourceCache a occ)[i]'(by rw [source_length];exact hi)=
      CloseoutRowsRawAtomLoop.indices (offset a occ i) (children a occ[i]).length := by
  have h:=cache_getElem 0 (counts a occ) i (by simpa only [counts_length] using hi)
  simpa only [sourceCache,counts,offset,List.map_take,Nat.zero_add,List.getElem_map] using h

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomCache
