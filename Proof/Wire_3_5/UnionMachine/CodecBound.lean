import Proof.Circuits.CanonicalWitnessCodec

/-! # C6: the atoms' size from their code (feasibility probe)

For "It rejects malformed descriptions, oversized atoms" (P3:3670) the union decodes every grid atom exactly (`decodeAtom`, base's canonical codec); the Theorem 2.5 repository's physical decoder (`CloseoutRowsCircuit{Threshold,Symmetric}Run`) also
bounds `wireCount ≤ W` and `descriptionBits ≤ L`, so the front docks it with bounds that no decodable atom of a short
code can exceed. This module proves that the canonical codec's size grows with the circuit.

The key step: **`nbl_pair`**, `nbl a + nbl b ≤ nbl (Nat.pair a b) + 1` (the pairing squares its larger argument), so a
balanced list's code has at least the summed bit lengths of its entries (**`nbl_balanced`**), and a tagged list's
code at least their sum less one per entry (**`nbl_tagged`**). The target (**`AtomBound`**): a decoded circuit of arity
`q` from a code of `ℓ` bits has `wireCount` and `descriptionBits` at most `C·(ℓ + q + 1)²`. Paper quantity: the atoms'
size, bounded by their code's length. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CodecBound
open NearCubicWires NearCubicWires.CanonicalBinary

/-! ## The pairing's bit length -/

theorem nbl_pos (n : ℕ) : 1 ≤ natBitLength n := by unfold natBitLength; omega

theorem nbl_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength; have := Nat.log_mono_right (b := 2) h; omega

/-- Squaring doubles the bit length, less one. -/
theorem nbl_sq (m : ℕ) : 2 * natBitLength m ≤ natBitLength (m * m) + 1 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [natBitLength]
  · unfold natBitLength
    have h1 := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    set k := Nat.log 2 m
    have h2 : 2 ^ (2 * k) ≤ m * m := by
      rw [show 2 * k = k + k by ring, pow_add]; exact Nat.mul_le_mul h1 h1
    have h3 : 2 * k ≤ Nat.log 2 (m * m) := by
      rw [Nat.le_log_iff_pow_le (by norm_num) (by positivity)]; exact h2
    omega

/-- **The pairing's bit length**: at least the two bit lengths, less one. -/
theorem nbl_pair (a b : ℕ) : natBitLength a + natBitLength b ≤ natBitLength (Nat.pair a b) + 1 := by
  unfold Nat.pair
  split_ifs with h
  · have e1 := nbl_sq b
    have e2 : natBitLength (b * b) ≤ natBitLength (b * b + a) := nbl_mono (by omega)
    have e3 : natBitLength a ≤ natBitLength b := nbl_mono (by omega)
    omega
  · have e1 := nbl_sq a
    have e2 : natBitLength (a * a) ≤ natBitLength (a * a + a + b) := nbl_mono (by omega)
    have e3 : natBitLength b ≤ natBitLength a := nbl_mono (by omega)
    omega

/-! ## Lists -/

/-- **A balanced list's code has at least its entries' summed bit lengths.** -/
theorem nbl_balanced : ∀ (k : ℕ) (l : List ℕ), l.length ≤ k →
    (l.map natBitLength).sum ≤ natBitLength (encodeBalancedList l)
  | _, [], _ => by simp [encodeBalancedList]
  | _, [x], _ => by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, encodeBalancedList]
    have := nbl_pair 1 x
    have h1 : natBitLength 1 = 1 := by decide
    omega
  | 0, _ :: _ :: _, h => by simp at h
  | k + 1, x :: y :: rest, h => by
    rw [encodeBalancedList]
    set values := x :: y :: rest with hv
    set L := values.take ((values.length + 1) / 2) with hL
    set R := values.drop ((values.length + 1) / 2) with hR
    have hlen : values.length = rest.length + 2 := by simp [hv]
    have hLl : L.length ≤ k := by simp [hL, hlen] at h ⊢; omega
    have hRl : R.length ≤ k := by simp [hR, hlen] at h ⊢; omega
    have iL := nbl_balanced k L hLl
    have iR := nbl_balanced k R hRl
    have p1 := nbl_pair 2 (Nat.pair (encodeBalancedList L) (encodeBalancedList R))
    have p2 := nbl_pair (encodeBalancedList L) (encodeBalancedList R)
    have h2 : natBitLength 2 = 2 := by decide
    have hsplit : (values.map natBitLength).sum = (L.map natBitLength).sum + (R.map natBitLength).sum := by
      rw [← List.sum_append, ← List.map_append, hL, hR, List.take_append_drop]
    omega

/-- The list's length is at most its code's bit length. -/
theorem length_le_balanced (l : List ℕ) : l.length ≤ natBitLength (encodeBalancedList l) := by
  have h := nbl_balanced l.length l le_rfl
  have : l.length ≤ (l.map natBitLength).sum := by
    have := List.length_le_sum_of_one_le (l.map natBitLength) (by
      intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact nbl_pos y)
    simpa using this
  omega

/-- **A tagged list's code has at least its entries' summed bit lengths, less one per entry.** -/
theorem nbl_tagged : ∀ (l : List ℕ), (l.map natBitLength).sum ≤ natBitLength (encodeTaggedList l) + l.length
  | [] => by simp [encodeTaggedList]
  | v :: rest => by
    simp only [List.map_cons, List.sum_cons, encodeTaggedList, List.length_cons]
    have i := nbl_tagged rest
    have p1 := nbl_pair 1 (Nat.pair v (encodeTaggedList rest))
    have p2 := nbl_pair v (encodeTaggedList rest)
    have h1 : natBitLength 1 = 1 := by decide
    omega

/-! ## Naturals, integers, gates -/

theorem nbl_le_size (m : ℕ) : natBitLength m ≤ m.size + 1 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [natBitLength]
  · unfold natBitLength
    have := Nat.lt_size_self m
    have := Nat.log_lt_of_lt_pow (b := 2) (by omega) this
    omega

theorem size_le_encodeNat (m : ℕ) : m.size ≤ natBitLength (encodeNat m) := by
  have h := length_le_balanced (m.bits.map boolCode)
  simp only [List.length_map] at h
  rw [← Nat.size_eq_bits_len]
  exact h

theorem intBitLength_le (z : ℤ) : intBitLength z ≤ natBitLength (encodeInt z) + 1 := by
  unfold intBitLength encodeInt
  have h1 := nbl_pair (if z < 0 then 1 else 0) (encodeNat z.natAbs)
  have h2 := size_le_encodeNat z.natAbs
  have h3 := nbl_le_size z.natAbs
  have h4 := nbl_pos (if z < 0 then 1 else 0)
  unfold natBitLength at h3
  omega

theorem sum_ofFn_le {n : ℕ} (f g : Fin n → ℕ) (h : ∀ i, f i ≤ g i) : ∑ i, f i ≤ ∑ i, g i :=
  Finset.sum_le_sum fun i _ => h i

theorem sum_ofFn_map {n : ℕ} (f : Fin n → ℕ) : ((List.ofFn f).map natBitLength).sum = ∑ i, natBitLength (f i) := by
  rw [List.map_ofFn, List.sum_ofFn]; rfl

/-- **A gate's size from its code**: `descriptionBits ≤ 4ℓ + 10`, `wireCount ≤ ℓ + 3` (`ℓ` its code's bit length). -/
theorem gate_bound {n : ℕ} (g : SupplierPipeline.SupportedNormalizedGate n) :
    g.descriptionBits ≤ 4 * natBitLength (SupplierPipeline.encodeSupportedNormalizedGate g) + 10 ∧
      g.wireCount ≤ natBitLength (SupplierPipeline.encodeSupportedNormalizedGate g) + 3 := by
  set W := encodeIntList (List.ofFn g.gate.weight) with hW
  set T := encodeInt g.gate.threshold with hT
  set M := encodeBoolList (List.ofFn fun index => decide (index ∈ g.support)) with hM
  have ht := nbl_tagged [W, T, M]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at ht
  have e : SupplierPipeline.encodeSupportedNormalizedGate g = encodeTaggedList [W, T, M] := rfl
  rw [e]
  -- the weights
  have hw := nbl_balanced _ ((List.ofFn g.gate.weight).map encodeInt) le_rfl
  have hWeq : natBitLength W = natBitLength (encodeBalancedList ((List.ofFn g.gate.weight).map encodeInt)) := rfl
  have hsumeq : (((List.ofFn g.gate.weight).map encodeInt).map natBitLength).sum =
      ∑ i, natBitLength (encodeInt (g.gate.weight i)) := by
    rw [List.map_map, List.map_ofFn, List.sum_ofFn]; rfl
  rw [hsumeq, ← hWeq] at hw
  have hw' : ∑ i, intBitLength (g.gate.weight i) ≤ ∑ i, (natBitLength (encodeInt (g.gate.weight i)) + 1) :=
    sum_ofFn_le _ _ fun i => intBitLength_le (g.gate.weight i)
  rw [Finset.sum_add_distrib] at hw'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hw'
  -- the arity
  have hn : n ≤ natBitLength M := by
    have := length_le_balanced ((List.ofFn fun index => decide (index ∈ g.support)).map boolCode)
    simpa [hM, encodeBoolList] using this
  have hT' := intBitLength_le g.gate.threshold
  rw [← hT] at hT'
  have hsupp : g.support.card ≤ n := by simpa using Finset.card_le_univ g.support
  refine ⟨?_, ?_⟩
  · show g.gate.encodingBits + n ≤ _
    unfold NormalizedThresholdGate.encodingBits
    omega
  · show g.support.card ≤ _
    omega

theorem sum_gates_le {n k : ℕ} (b : Fin k → SupplierPipeline.SupportedNormalizedGate n) :
    ∑ i, natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (b i)) ≤
      natBitLength (encodeBalancedList (List.ofFn fun i => SupplierPipeline.encodeSupportedNormalizedGate (b i))) := by
  have h := nbl_balanced _ (List.ofFn fun i => SupplierPipeline.encodeSupportedNormalizedGate (b i)) le_rfl
  rwa [sum_ofFn_map] at h

theorem count_le {n k : ℕ} (b : Fin k → SupplierPipeline.SupportedNormalizedGate n) :
    k ≤ natBitLength (encodeBalancedList (List.ofFn fun i => SupplierPipeline.encodeSupportedNormalizedGate (b i))) := by
  have h := length_le_balanced (List.ofFn fun i => SupplierPipeline.encodeSupportedNormalizedGate (b i))
  simpa using h

/-! ## Circuits -/

theorem thr_bound {q : ℕ} (c : SupplierPipeline.NormalizedThresholdThresholdCircuit q) :
    c.wireCount ≤ 20 * (natBitLength (SupplierPipeline.encodeNormalizedThresholdThresholdCircuit c) + 4) ∧
      c.descriptionBits ≤ 20 * (natBitLength (SupplierPipeline.encodeNormalizedThresholdThresholdCircuit c) + 4) := by
  set B := encodeBalancedList (List.ofFn fun i => SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) with hB
  set Tp := SupplierPipeline.encodeSupportedNormalizedGate c.top with hTp
  have ht := nbl_tagged [encodeNat SupplierPipeline.thresholdCircuitFamilyTag, encodeNat c.bottomCount, B, Tp]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at ht
  have e : SupplierPipeline.encodeNormalizedThresholdThresholdCircuit c =
      encodeTaggedList [encodeNat SupplierPipeline.thresholdCircuitFamilyTag, encodeNat c.bottomCount, B, Tp] := rfl
  rw [e]
  have hsum := sum_gates_le c.bottom
  have hk := count_le c.bottom
  rw [← hB] at hsum hk
  have hgates : ∀ i, (c.bottom i).descriptionBits ≤ 4 * natBitLength
      (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + 10 ∧
      (c.bottom i).wireCount ≤ natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + 3 :=
    fun i => gate_bound (c.bottom i)
  have htop := gate_bound c.top
  rw [← hTp] at htop
  have h1 := nbl_pos (encodeNat SupplierPipeline.thresholdCircuitFamilyTag)
  have h2 := nbl_pos (encodeNat c.bottomCount)
  refine ⟨?_, ?_⟩
  · show ∑ i ∈ c.top.support, ((c.bottom i).wireCount + 1) ≤ _
    have a1 : ∑ i ∈ c.top.support, ((c.bottom i).wireCount + 1) ≤ ∑ i, ((c.bottom i).wireCount + 1) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have a2 : ∑ i, ((c.bottom i).wireCount + 1) ≤
        ∑ i, (natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + 4) :=
      sum_ofFn_le _ _ fun i => by have := (hgates i).2; omega
    have a3 : ∑ i, (natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + 4) =
        ∑ i, natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + c.bottomCount * 4 := by
      rw [Finset.sum_add_distrib]; simp
    omega
  · show c.top.descriptionBits + ∑ i, (c.bottom i).descriptionBits ≤ _
    have a2 : ∑ i, (c.bottom i).descriptionBits ≤
        ∑ i, (4 * natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + 10) :=
      sum_ofFn_le _ _ fun i => (hgates i).1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at a2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at a2
    omega

theorem sym_bound {q : ℕ} (c : SupplierPipeline.NormalizedSymmetricThresholdCircuit q) :
    c.wireCount ≤ 20 * (natBitLength (SupplierPipeline.encodeNormalizedSymmetricThresholdCircuit c) + 4) ∧
      c.descriptionBits ≤ 20 * (natBitLength (SupplierPipeline.encodeNormalizedSymmetricThresholdCircuit c) + 4) := by
  set B := encodeBalancedList (List.ofFn fun i => SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) with hB
  set Tp := encodeBoolList (List.ofFn c.top) with hTp
  have ht := nbl_tagged [encodeNat SupplierPipeline.symmetricCircuitFamilyTag, encodeNat c.bottomCount, B, Tp]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at ht
  have e : SupplierPipeline.encodeNormalizedSymmetricThresholdCircuit c =
      encodeTaggedList [encodeNat SupplierPipeline.symmetricCircuitFamilyTag, encodeNat c.bottomCount, B, Tp] := rfl
  rw [e]
  have hsum := sum_gates_le c.bottom
  have hk := count_le c.bottom
  rw [← hB] at hsum hk
  have hgates : ∀ i, (c.bottom i).descriptionBits ≤ 4 * natBitLength
      (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + 10 ∧
      (c.bottom i).wireCount ≤ natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + 3 :=
    fun i => gate_bound (c.bottom i)
  have h1 := nbl_pos (encodeNat SupplierPipeline.symmetricCircuitFamilyTag)
  have h2 := nbl_pos (encodeNat c.bottomCount)
  have h4 := nbl_pos Tp
  refine ⟨?_, ?_⟩
  · show ∑ i, ((c.bottom i).wireCount + 1) ≤ _
    have a2 : ∑ i, ((c.bottom i).wireCount + 1) ≤
        ∑ i, (natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + 4) :=
      sum_ofFn_le _ _ fun i => by have := (hgates i).2; omega
    have a3 : ∑ i, (natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + 4) =
        ∑ i, natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + c.bottomCount * 4 := by
      rw [Finset.sum_add_distrib]; simp
    omega
  · show c.bottomCount + 1 + ∑ i, (c.bottom i).descriptionBits ≤ _
    have a2 : ∑ i, (c.bottom i).descriptionBits ≤
        ∑ i, (4 * natBitLength (SupplierPipeline.encodeSupportedNormalizedGate (c.bottom i)) + 10) :=
      sum_ofFn_le _ _ fun i => (hgates i).1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at a2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at a2
    omega

/-! ## The target -/

/-- **The atoms' size bound**: every decodable atom's wire count and description length are at most `20·(ℓ + 4)` in
its code's bit length `ℓ` (both class modes). -/
theorem atomBound_thr (q v : ℕ) (c : SupplierPipeline.NormalizedThresholdThresholdCircuit q)
    (h : CanonicalWitnessCodec.decodeNormalizedThresholdThresholdCircuit q v = some c) :
    c.wireCount ≤ 20 * (natBitLength v + 4) ∧ c.descriptionBits ≤ 20 * (natBitLength v + 4) := by
  have e := CanonicalWitnessCodec.encodeNormalizedThresholdThresholdCircuit_of_decode h
  rw [← e]; exact thr_bound c

theorem atomBound_sym (q v : ℕ) (c : SupplierPipeline.NormalizedSymmetricThresholdCircuit q)
    (h : CanonicalWitnessCodec.decodeNormalizedSymmetricThresholdCircuit q v = some c) :
    c.wireCount ≤ 20 * (natBitLength v + 4) ∧ c.descriptionBits ≤ 20 * (natBitLength v + 4) := by
  have e := CanonicalWitnessCodec.encodeNormalizedSymmetricThresholdCircuit_of_decode h
  rw [← e]; exact sym_bound c


end NearCubicWires.WireExponent3_5.UnionMachine.CodecBound
