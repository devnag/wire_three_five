import Proof.CaseAnalysis.RowsCircuitBottomMeaning

/-! P25: the frozen semantic input of the ordered decomposition-source batch.
Everything is stated with the existing definitions: the same selected
constructor `a.output`, the same bottom request `CloseoutRowsGateSource.request false`,
the checked `nativeWord`, and the two BottomMeaning output lists. No new
decomposition, no decoded output, no compression of arity to support. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open SupplierPipeline CompilerSemantics CanonicalWitnessCodec RadixSemantics
open RepairOrdinary.DecompositionSource RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)

/-- The ordinary bottom request of one retained occurrence (arity `q`, weak-to-strict). -/
def request {q : ℕ} (g : SupportedNormalizedGate q) : ExactDecompositionRequest :=
  CloseoutRowsGateSource.request false g
/-- The exact ordered children the selected constructor returns for that request. -/
def children {q : ℕ} (g : SupportedNormalizedGate q) : List (ExactThresholdGate q) :=
  (a.output (request g)).children
/-- The concatenated native child cache in occurrence order. -/
def GS {q : ℕ} (occ : List (SupportedNormalizedGate q)) : List (ExactThresholdGate q) :=
  occ.flatMap (children a)
/-- The per-occurrence child counts in the same order (zeros keep their position). -/
def counts {q : ℕ} (occ : List (SupportedNormalizedGate q)) : List ℕ :=
  occ.map (fun g => (children a g).length)
/-- The total child count. -/
def B {q : ℕ} (occ : List (SupportedNormalizedGate q)) : ℕ := (GS a occ).length
/-- Children of occurrences before `i`. -/
def offset {q : ℕ} (occ : List (SupportedNormalizedGate q)) (i : ℕ) : ℕ :=
  ((occ.take i).map (fun g => (children a g).length)).sum
/-- The validated circuit's native bottom stream: count header, framed opaque top
payload, then one framed native word per retained occurrence in order. -/
def segment {q : ℕ} (occ : List (SupportedNormalizedGate q)) (top : List Bool) : List Bool :=
  natWord occ.length ++ frame top ++ occ.flatMap (fun g => frame (nativeWord g))

/-! ## Request identity and the strict convention -/

theorem request_arity {q : ℕ} (g : SupportedNormalizedGate q) : (request g).arity = q := rfl
theorem nativeWord_eq {q : ℕ} (g : SupportedNormalizedGate q) :
    nativeWord g = thresholdWord (request g).gate := rfl
/-- The framed native word is exactly the constructor's framed input word. -/
theorem nativeWord_input {q : ℕ} (g : SupportedNormalizedGate q) :
    nativeWord g = natWord (request g).arity ++ DecompositionSource.Call.tail (request g) := by
  simp only [nativeWord_eq, thresholdWord, DecompositionSource.Call.tail, request_arity, List.append_assoc]

/-! ## Counts, totals, offsets -/

theorem counts_length {q : ℕ} (occ : List (SupportedNormalizedGate q)) : (counts a occ).length = occ.length := by
  simp [counts]
theorem B_eq_sum {q : ℕ} (occ : List (SupportedNormalizedGate q)) : B a occ = (counts a occ).sum := by
  simp [B, GS, counts, List.length_flatMap]
theorem GS_cons {q : ℕ} (g : SupportedNormalizedGate q) (occ : List (SupportedNormalizedGate q)) :
    GS a (g :: occ) = children a g ++ GS a occ := by simp [GS]
theorem counts_cons {q : ℕ} (g : SupportedNormalizedGate q) (occ : List (SupportedNormalizedGate q)) :
    counts a (g :: occ) = (children a g).length :: counts a occ := by simp [counts]

/-! ## The existing raw-rows child identity and pair-coded assignment -/

/-! ## Cache word and the direct-bank native port -/

/-! ## The two actual modes: exactly the checked BottomMeaning lists -/



/-! ## Source-fixed bounds from the actual request word -/

theorem parameter_le_word {q : ℕ} (g : SupportedNormalizedGate q) :
    (request g).arity + (request g).gate.encodingBits + 1 ≤ (nativeWord g).length := by
  change q + (nonStrictAsStrict g.gate).encodingBits + 1 ≤ (thresholdWord (nonStrictAsStrict g.gate)).length
  rw [thresholdWord_length]
  omega

theorem word_le_frame (w : List Bool) : w.length ≤ (frame w).length := by
  rw [frame_length']; omega

theorem sourceBudget_le_frame {q : ℕ} (g : SupportedNormalizedGate q) :
    sourceBudget a (request g) ≤ a.coefficient * (frame (nativeWord g)).length ^ a.degree := by
  unfold sourceBudget
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  exact (parameter_le_word g).trans (word_le_frame _)

theorem children_le_budget {q : ℕ} (g : SupportedNormalizedGate q) :
    (children a g).length ≤ sourceBudget a (request g) :=
  (children_le_output _).trans (output_length a (request g))

theorem body_le_budget {q : ℕ} (g : SupportedNormalizedGate q) :
    ((children a g).flatMap exactWord).length ≤ sourceBudget a (request g) := by
  have h := output_length a (request g)
  rw [exactListWord, List.length_append] at h
  exact le_trans (Nat.le_add_left _ _) h

theorem cache_le_budget {q : ℕ} (g : SupportedNormalizedGate q) :
    (exactListWord (children a g)).length ≤ sourceBudget a (request g) := output_length a (request g)

/-- Every framed gate word is a sub-block of the frame region of its segment. -/
theorem frame_le_region {q : ℕ} (occ : List (SupportedNormalizedGate q)) (g : SupportedNormalizedGate q)
    (hg : g ∈ occ) : (frame (nativeWord g)).length ≤ (occ.flatMap (fun g => frame (nativeWord g))).length := by
  induction occ with
  | nil => simp at hg
  | cons h occ ih =>
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hg with rfl | hg
    · omega
    · have := ih hg; omega

theorem segment_length {q : ℕ} (occ : List (SupportedNormalizedGate q)) (top : List Bool) :
    (segment occ top).length =
      (natWord occ.length).length + (frame top).length + (occ.flatMap (fun g => frame (nativeWord g))).length := by
  simp only [segment, List.length_append]

theorem length_le_region {q : ℕ} (occ : List (SupportedNormalizedGate q)) :
    occ.length ≤ (occ.flatMap (fun g => frame (nativeWord g))).length := by
  induction occ with
  | nil => simp
  | cons g occ ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := frame_pos (nativeWord g)
    omega


end NearCubicWires.ExtDecompositionBatch
