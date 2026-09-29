import Proof.CaseAnalysis.RowsGateFieldsMeaning
import Proof.Wire_3_5.Foundations.Carrier

/-! # The carrier code's format (P3:3071-3086)

"Fix a polynomial global family of named carriers [...] For a fixed tuple of circuits `C_1,…,C_a` in either class
mode, whose gates are contained in these carriers" (P3:3071-3086). A primitive call names its carriers by their codes
(`PrimRequest.word` carries `natListWord (r.carriers.map Carrier.code)`). The union front WRITES a carrier's code from
the codes of the circuits it collects (C6's `CarrierWriter`), and the primitive READS the code back into the gate
table of its mask (the carrier decoder). This module is the layout both sides share:

* `gateCode g`: the code of one atom, the tagged pair `[encodeIntList w, encodeInt θ]`; **`code_eq`**: a carrier's
  code is the balanced list of its atoms' codes;
* the field boundaries of an atom code: `gateCode_pair` (the pairing cells `⟨1, w, 1, θ, 0⟩`); for any word whose
  value is an atom code, base's triple extractor (`CompetitorWitnessTriple`, the header of `CloseoutRowsGateHeader`)
  reads the tags at fields 0 and 2, the weight list at field 1, the threshold at field 3 and the empty tail `0` at
  fields 4, 5 and node 6 (`gate_fields`); the gate header's three field words are the weight list, the threshold and
  `0` (`gate_codeWords`); the signed threshold and the weight list as pairs (`threshold_pair`, `weights_list`);
* the decoders' round trips (`decode_code`, `tree_atoms_code`, `atomStream_code`, `decodeTaggedList_gateCode`,
  `decode_weights`, `decode_threshold`);
* the writer's sources: a supported gate's code (`encodeSupportedNormalizedGate`) carries the atom's two fields first
  (`supported_fields`), so an atom's code is the tagged pair of the first two fields of the bottom code it comes from
  (`gateCode_supported`, and on the header's field words, `supported_codeWords`); the bottoms' codes sit at field 2
  of a circuit code (`sym_fields`, `thr_fields`); the charged gates' codes (`symGates_codes`, `thrGates_codes`);
  a carrier collected from several circuits is the balanced list of their atoms' codes, in order (`code_flatten`).

Paper quantity of the main types: the carrier code `Carrier.code X`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.CarrierFormat
open NearCubicWires NearCubicWires.CanonicalBinary NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.RepairOrdinary

/-! ## The code of a carrier -/

/-- **The code of one carrier atom**: its weight list and its threshold, as a tagged pair (the summand of
`Carrier.code`). -/
def gateCode {n : ℕ} (g : NormalizedThresholdGate n) : ℕ :=
  encodeTaggedList [encodeIntList (List.ofFn g.weight), encodeInt g.threshold]

/-- **A carrier's code is the balanced list of its atoms' codes.** -/
theorem code_eq {n : ℕ} (X : Carrier n) : X.code = encodeBalancedList (X.map gateCode) := rfl

/-- The pairing cells of an atom code: the tag `1`, the weight list, the tag `1`, the threshold, the empty tail. -/
theorem gateCode_pair {n : ℕ} (g : NormalizedThresholdGate n) :
    gateCode g = Nat.pair 1 (Nat.pair (encodeIntList (List.ofFn g.weight))
      (Nat.pair 1 (Nat.pair (encodeInt g.threshold) 0))) := rfl

/-! ## The field boundaries -/

/-- **The field boundaries of an atom code** as base's triple extractor reads them: the tags at fields 0 and 2, the
weight list at field 1, the threshold at field 3, and the empty tail `0` at fields 4, 5 and node 6. -/
theorem gate_fields {n : ℕ} (g : NormalizedThresholdGate n) (bits : List Bool)
    (h : RadixSemantics.value bits = gateCode g) :
    CompetitorWitnessTriple.field bits 0 = 1 ∧
      CompetitorWitnessTriple.field bits 1 = encodeIntList (List.ofFn g.weight) ∧
      CompetitorWitnessTriple.field bits 2 = 1 ∧ CompetitorWitnessTriple.field bits 3 = encodeInt g.threshold ∧
      CompetitorWitnessTriple.field bits 4 = 0 ∧ CompetitorWitnessTriple.field bits 5 = 0 ∧
      CompetitorWitnessTriple.node bits 6 = 0 := by
  simp only [CompetitorWitnessTriple.field_eq, CompetitorWitnessTriple.node_eq, h, CompetitorWitnessTriple.nodeCode,
    gateCode_pair, Nat.unpair_pair, Nat.unpair_zero, Prod.fst_zero, Prod.snd_zero]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- **The gate header's three field words on an atom code**: the weight list, the threshold, and `0`. -/
theorem gate_codeWords {n : ℕ} (g : NormalizedThresholdGate n) (bits : List Bool)
    (h : RadixSemantics.value bits = gateCode g) :
    RadixSemantics.value (CloseoutRowsGateHeader.codeWord bits 0) = encodeIntList (List.ofFn g.weight) ∧
      RadixSemantics.value (CloseoutRowsGateHeader.codeWord bits 1) = encodeInt g.threshold ∧
      RadixSemantics.value (CloseoutRowsGateHeader.codeWord bits 2) = 0 := by
  obtain ⟨_, h1, _, h3, _, h5, _⟩ := gate_fields g bits h
  exact ⟨h1, h3, h5⟩

/-! ## The decoders' round trips -/

/-- The balanced traversal's atoms of a carrier code are its atoms' codes. -/
theorem tree_atoms_code {n : ℕ} (X : Carrier n) :
    (PCPPNativeCanonicalTree.tree X.code).atoms = X.map gateCode :=
  PCPPNativeCanonicalTree.tree_atoms _

/-- **The atom stream of a carrier code** (what base's traversal writes): the atoms' codes as `w`-bit framed words. -/
theorem atomStream_code {n : ℕ} (w : ℕ) (X : Carrier n) :
    PCPPNativeCanonicalWalk.atomStream w (PCPPNativeCanonicalTree.tree X.code).atoms =
      X.flatMap fun g => frame (SignedSortKey.binary w (gateCode g)) := by
  rw [tree_atoms_code, PCPPNativeCanonicalWalk.atomStream, List.flatMap_map]

theorem decode_weights {n : ℕ} (g : NormalizedThresholdGate n) :
    decodeIntList (encodeIntList (List.ofFn g.weight)) = some (List.ofFn g.weight) :=
  decodeIntList_encode _

theorem decode_threshold {n : ℕ} (g : NormalizedThresholdGate n) :
    decodeInt (encodeInt g.threshold) = some g.threshold :=
  decodeInt_encode _

/-! ## The writer's sources -/

/-- The same on the gate header's field words of a bottom code (base `field_codes`). -/
theorem supported_codeWords {n : ℕ} (sg : SupportedNormalizedGate n) (bits : List Bool)
    (h : RadixSemantics.value bits = encodeSupportedNormalizedGate sg) :
    gateCode sg.gate = encodeTaggedList [RadixSemantics.value (CloseoutRowsGateHeader.codeWord bits 0),
      RadixSemantics.value (CloseoutRowsGateHeader.codeWord bits 1)] := by
  obtain ⟨_, hc⟩ := CloseoutRowsGateFieldsMeaning.field_codes sg bits h
  rw [hc 0, hc 1]
  rfl

/-- The atoms' codes of a `SYM∘THR` circuit's charged gates: every bottom's, in order. -/
theorem symGates_codes {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) :
    (symGates C).map gateCode = List.ofFn fun i => gateCode (C.bottom i).gate := by
  simp only [symGates, List.map_map, List.ofFn_eq_map, Function.comp_def]

/-- The atoms' codes of a `THR∘THR` circuit's charged gates: the retained bottoms' (the top's support), in order. -/
theorem thrGates_codes {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) :
    (thrGates C).map gateCode = ((List.finRange C.bottomCount).filter fun i => decide (i ∈ C.top.support)).map
      fun i => gateCode (C.bottom i).gate := by
  simp only [thrGates, List.map_map, Function.comp_def]

end NearCubicWires.WireExponent3_5.PrimT.CarrierFormat
