import Proof.Wire_3_5.UnionMachine.FrontSemSize

/-! # C6 front, the semantic core (11): a carrier's gates are bounded by its code (P3:3409-3410, 3673)

A carrier's canonical code (a balanced list of its gates' tagged codes) bounds its gate count and every gate's
weight and threshold bits (**`carrier_bits`**, `gate_bits`, CodecBound's `nbl_balanced` / `nbl_tagged`), hence C1's
request words of its gates (**`selGates_len`**) and the converter's words and capacity (**`capNeed_le`**).

Paper quantity: the named carriers' gates (their weights and thresholds) against the carrier code. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemGate
open NearCubicWires NearCubicWires.CanonicalBinary NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.UnionMachine.CodecBound

/-- A gate's tagged code (the carrier code's entry). -/
def gcode {q : ℕ} (g : NormalizedThresholdGate q) : ℕ :=
  encodeTaggedList [encodeIntList (List.ofFn g.weight), encodeInt g.threshold]

theorem nbl_succ_le (n : ℕ) : natBitLength (n + 1) ≤ natBitLength n + 1 := by
  unfold natBitLength
  have h : n + 1 < 2 ^ (Nat.log 2 n + 2) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    rw [pow_succ] at this ⊢; omega
  have := Nat.log_lt_of_lt_pow (by omega) h
  omega

/-- **A gate's weight and threshold bits** from its code. -/
theorem gate_bits {q : ℕ} (g : NormalizedThresholdGate q) :
    ((List.ofFn g.weight).map intBitLength).sum + intBitLength g.threshold ≤ natBitLength (gcode g) + q + 3 := by
  have ht := nbl_tagged [encodeIntList (List.ofFn g.weight), encodeInt g.threshold]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at ht
  have hw := nbl_balanced _ ((List.ofFn g.weight).map encodeInt) le_rfl
  have e1 : natBitLength (encodeIntList (List.ofFn g.weight)) =
      natBitLength (encodeBalancedList ((List.ofFn g.weight).map encodeInt)) := rfl
  have hsum : ((List.ofFn g.weight).map intBitLength).sum ≤
      (((List.ofFn g.weight).map encodeInt).map natBitLength).sum + q := by
    rw [List.map_map]
    have key : ∀ l : List ℤ, (l.map intBitLength).sum ≤ (l.map (natBitLength ∘ encodeInt)).sum + l.length := by
      intro l
      induction l with
      | nil => simp
      | cons z l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp]
        have := intBitLength_le z
        omega
    have := key (List.ofFn g.weight)
    rw [List.length_ofFn] at this
    exact this
  have hT := intBitLength_le g.threshold
  unfold gcode
  omega

/-- A gate's request word in C1's format. -/
theorem selGate_len {q : ℕ} (g : NormalizedThresholdGate q) :
    (GateConv.selGate g).length ≤ 2 * natBitLength (gcode g) + 4 * q + 8 := by
  have hb := gate_bits g
  have e : (GateConv.selGate g).length = 2 * (((List.ofFn g.weight).map intBitLength).sum + intBitLength g.threshold) +
      2 * q + 2 := by
    unfold GateConv.selGate
    rw [List.length_append, List.length_flatMap, GateConv.intWord_len']
    have key : ∀ l : List ℤ, (l.map fun z => (RepairRepresentation.intWord z).length).sum =
        2 * (l.map intBitLength).sum + 2 * l.length := by
      intro l
      induction l with
      | nil => simp
      | cons z l ih =>
        rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons, ih, GateConv.intWord_len']
        unfold intBitLength natBitLength; ring
    rw [key, List.length_ofFn]
    unfold intBitLength natBitLength; ring
  omega

/-- **The carrier code bounds its gates**: their count and their codes' summed bits. -/
theorem carrier_bits {q : ℕ} (X : Stars.Carrier q) :
    (X.map fun g => natBitLength (gcode g)).sum ≤ natBitLength (Stars.Carrier.code X) ∧
      X.length ≤ natBitLength (Stars.Carrier.code X) := by
  have h1 := nbl_balanced _ (X.map gcode) le_rfl
  have h2 := length_le_balanced (X.map gcode)
  rw [List.map_map, List.length_map] at *
  exact ⟨h1, h2⟩

/-- **C1's request words of a carrier's gates.** -/
theorem selGates_len {q : ℕ} (X : Stars.Carrier q) :
    (X.flatMap GateConv.selGate).length ≤ (4 * q + 10) * natBitLength (Stars.Carrier.code X) := by
  obtain ⟨h1, h2⟩ := carrier_bits X
  rw [List.length_flatMap]
  have key : ∀ l : List (NormalizedThresholdGate q), (l.map fun g => (GateConv.selGate g).length).sum ≤
      2 * (l.map fun g => natBitLength (gcode g)).sum + (4 * q + 8) * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := selGate_len g
      rw [Nat.mul_add, Nat.mul_add, mul_one]; omega
  have := key X
  have e : (4 * q + 10) * natBitLength (Stars.Carrier.code X) =
      2 * natBitLength (Stars.Carrier.code X) + (4 * q + 8) * natBitLength (Stars.Carrier.code X) := by ring
  have := Nat.mul_le_mul_left (4 * q + 8) h2
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemGate
