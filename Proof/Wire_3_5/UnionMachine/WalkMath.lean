import Proof.Wire_3_5.Primitive.SeedFix.WalkBankIface

/-! # C6 tail, item 3 (part 1): the walk sample's index word and bank

"Pad the base seed to an even number of bits and use the explicit powered Margulis walk [...] The walk starts
uniformly" and "the seed consists of the initial base seed and `O(t)` edge-label bits" (P3:2083-2087, 2098-2100). The
index word of a walk sample (base's executable enumeration, `positiveWalkSampleFinEquiv`) is, at every side width `r`,
the edge labels' word, then the start vertex's second and first coordinates (**`index_word`**, base's
`WalkSampleWord.binary_eq` at the Toeplitz width, here for every `r`); the walk's entry bank at time `0` is the start
vertex's padded coordinate words, the unary work tapes and the labels' word (**`bank_eq`**).

Paper quantity of the main types: the walk sample's start vertex and edge labels (its index word and entry bank). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.WalkMath
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces Theorem25Completion

/-- The start vertex's word: its second coordinate, then its first (`r` bits each, low bit first). -/
def vtxWord (r : ℕ) (v : MargulisVertex (2 ^ r)) : List Bool := binary r v.2.val ++ binary r v.1.val

theorem index_value (r n : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) :
    value (WalkSampleWord.labelsWord (sampleTransitionLabels sample) ++ vtxWord r sample.start) =
      (positiveWalkSampleFinEquiv (2 ^ r) n sample).val := by
  rw [value_append, WalkSampleWord.labels_value, WalkSampleWord.labels_length, vtxWord, value_append,
    binary_length, binary_value _ _ (ZMod.val_lt sample.start.2), binary_value _ _ (ZMod.val_lt sample.start.1)]
  have hp : 2 ^ (160 * n) = Fintype.card PoweredMargulisLabel ^ n := by
    rw [FrozenWalkABI.label_cardinality, pow_mul]
  rw [hp]
  simp only [positiveWalkSampleFinEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    Equiv.prodCongr_apply, finProdFinEquiv_apply_val, positiveSampleEquiv, margulisVertexFinEquiv,
    Equiv.coe_fn_mk, Prod.map_fst, Prod.map_snd]
  have h1 := Completion.ToeplitzSeedBits.finEquiv_symm_val sample.start.1
  have h2 := Completion.ToeplitzSeedBits.finEquiv_symm_val sample.start.2
  change _ = _ + _ * (((ZMod.finEquiv _).symm sample.start.2).val + 2 ^ r * ((ZMod.finEquiv _).symm sample.start.1).val)
  rw [h1, h2]

/-- **The index word**: the labels' word, then the start vertex's word. -/
theorem index_word (r n : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) :
    PrimT.WalkBank.seedIndexWord r n sample =
      WalkSampleWord.labelsWord (sampleTransitionLabels sample) ++ vtxWord r sample.start := by
  have h := BoundedCounter.binary_of_value (WalkSampleWord.labelsWord (sampleTransitionLabels sample) ++
    vtxWord r sample.start)
  have hl : (WalkSampleWord.labelsWord (sampleTransitionLabels sample) ++ vtxWord r sample.start).length =
      160 * n + 2 * r := by
    rw [List.length_append, WalkSampleWord.labels_length, vtxWord, List.length_append, binary_length,
      binary_length]
    try omega
  rw [hl, index_value] at h
  exact h

theorem vertex_zero (r n : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) :
    WalkTimeLoop.vertex sample 0 = sample.start := by
  simp only [WalkTimeLoop.vertex, Nat.min_eq_left (Nat.zero_le n)]
  rw [MargulisWalkSample.vertex.eq_def]

/-- **The entry bank at time `0`**: the start vertex's padded coordinate words, the work tapes, the labels' word. -/
theorem bank_eq (r n R L : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) :
    WalkTimeLoop.A R L sample [] 0 = Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool)
      ![ZeroPadding.pad R (frame (binary r sample.start.1.val)), ZeroPadding.pad R (frame (binary r sample.start.2.val)),
        List.replicate R false, List.replicate L false, List.replicate R true, UnaryTemplate.tape R,
        List.replicate (R + 1) false]
      (fun _ => WalkSampleWord.labelsWord (sampleTransitionLabels sample)) := by
  unfold WalkTimeLoop.A WalkLabelDispatch.bank WalkEdgeCanonical.input WalkEdgeReuse.word
  rw [vertex_zero, List.append_nil]
  rfl

end NearCubicWires.WireExponent3_5.UnionMachine.WalkMath
