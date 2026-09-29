import Proof.Wire_3_5.FinalPass.PoolFit3
import Proof.Wire_3_5.FinalPass.SymHr

/-! # The SYM pool's coefficient width: `h = dH·(n+1)^{eH}` fits the pool

"Constants, complemented atoms, and the systematic encoding parity are permitted at the same fixed description
envelope" (P3:3092-3094) and alg:disjoint's child bits (P3:1596-1615): at a SYM call every pool gate (a carrier atom,
its complement `negGate`, or a circuit's bottom gate) has at most `(n+1)^{26} + 1` encoding bits, so the decomposition
algorithm's budget at every pool gate is at most `symBud a n = coefficient·(n + (n+1)^{26} + 3)^{degree}`, and
`h = dH·(n+1)^{eH}` with `dH = coefficient·4^{degree} + 2`, `eH = 26·degree + 1` fits the pool.
* `intBitLength_add_one_le`, `enc_negGate`, `enc_nonStrict`, **`symPool_bits`**, `symBud`, **`sym_budget_le`**,
  **`symBud_le`**, **`symPoolFits`**.
Paper quantities of the main types: the SYM pool's coefficient bits against `h`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine

theorem intBitLength_le_of {z w : ℤ} (h : w.natAbs ≤ z.natAbs + 1) : intBitLength w ≤ intBitLength z + 1 := by
  unfold intBitLength
  rcases Nat.eq_zero_or_pos z.natAbs with hz | hz
  · rw [hz] at h ⊢
    have : Nat.log 2 w.natAbs ≤ 0 := by
      rcases Nat.lt_or_ge w.natAbs 2 with h2 | h2
      · exact le_of_eq (Nat.log_of_lt h2)
      · omega
    omega
  · have h1 : w.natAbs ≤ 2 * z.natAbs := by omega
    have h2 : Nat.log 2 w.natAbs ≤ Nat.log 2 (2 * z.natAbs) := Nat.log_mono_right h1
    have h3 : Nat.log 2 (2 * z.natAbs) = Nat.log 2 z.natAbs + 1 := by
      rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
    omega

theorem enc_negGate {n : ℕ} (g : NormalizedThresholdGate n) :
    (Corner.negGate g).encodingBits ≤ g.encodingBits + 1 := by
  unfold NormalizedThresholdGate.encodingBits Corner.negGate
  have h1 : intBitLength (1 - g.threshold) ≤ intBitLength g.threshold + 1 := intBitLength_le_of (by omega)
  have h2 : ∀ i, intBitLength (-g.weight i) = intBitLength (g.weight i) := fun i => by simp [intBitLength]
  simp only [h2]
  omega

theorem enc_nonStrict {n : ℕ} (g : NormalizedThresholdGate n) :
    (CompilerSemantics.nonStrictAsStrict g).encodingBits ≤ g.encodingBits + 1 := by
  unfold NormalizedThresholdGate.encodingBits CompilerSemantics.nonStrictAsStrict
  have h1 : intBitLength (g.threshold - 1) ≤ intBitLength g.threshold + 1 := intBitLength_le_of (by omega)
  simp only
  omega

/-- **Every SYM pool gate has at most `(n+1)^{26} + 1` encoding bits** (the call's envelopes). -/
theorem symPool_bits {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (hcar : ∀ X ∈ carriers, X.WithinEnvelope 26) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    ∀ g ∈ Records.symPool Cs carriers, g.encodingBits ≤ (n + 1) ^ 26 + 1 := by
  intro g hg
  unfold Records.symPool Records.symSlices at hg
  obtain ⟨sl, hsl, hg⟩ := List.mem_flatten.mp hg
  rcases List.mem_append.mp hsl with hX | hC
  · obtain ⟨X, hXc, rfl⟩ := List.mem_map.mp hX
    unfold Corner.maskGates at hg
    obtain ⟨g0, hg0, hgg⟩ := List.mem_flatMap.mp hg
    have hb := (hcar X hXc).2 g0 hg0
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hgg
    rcases hgg with rfl | rfl
    · omega
    · have := enc_negGate g0; omega
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hC
    unfold symGates at hg
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
    have h1 := hd i
    unfold NormalizedSymmetricThresholdCircuit.descriptionBits at h1
    have h2 : ((Cs i).bottom j).descriptionBits ≤ ∑ k, ((Cs i).bottom k).descriptionBits :=
      Finset.single_le_sum (f := fun k => ((Cs i).bottom k).descriptionBits) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have h3 : ((Cs i).bottom j).gate.encodingBits ≤ ((Cs i).bottom j).descriptionBits := by
      unfold SupportedNormalizedGate.descriptionBits; omega
    show ((Cs i).bottom j).gate.encodingBits ≤ _
    omega

/-- The SYM pool's budget bound. -/
def symBud (a : RepairRepresentation.DecompositionAlgorithm) (n : ℕ) : ℕ :=
  a.coefficient * (n + ((n + 1) ^ 26 + 2) + 1) ^ a.degree

/-- **Every SYM pool gate's decomposition budget is at most `symBud a n`.** -/
theorem sym_budget_le (a : RepairRepresentation.DecompositionAlgorithm) {n a' : ℕ}
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (hcar : ∀ X ∈ carriers, X.WithinEnvelope 26) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    ∀ g ∈ (Records.symPool Cs carriers).map PrimT.C4Geo.suppG,
      RepairOrdinary.DecompositionSource.sourceBudget a (ExtDecompositionBatch.request g) ≤ symBud a n := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  have hb := symPool_bits Cs carriers hcar hd g0 hg0
  have hn := enc_nonStrict g0
  unfold RepairOrdinary.DecompositionSource.sourceBudget symBud
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  show n + (CompilerSemantics.nonStrictAsStrict g0).encodingBits + 1 ≤ _
  omega

/-- **`symBud a n + n + 2 ≤ (coefficient·4^{degree} + 2)·(n+1)^{26·degree + 1}`.** -/
theorem symBud_le (a : RepairRepresentation.DecompositionAlgorithm) (n : ℕ) :
    symBud a n + n + 2 ≤ (a.coefficient * 4 ^ a.degree + 2) * (n + 1) ^ (26 * a.degree + 1) := by
  unfold symBud
  have hN : 1 ≤ (n + 1) ^ 26 := Nat.one_le_pow _ _ (by omega)
  have h1 : n + ((n + 1) ^ 26 + 2) + 1 ≤ 4 * (n + 1) ^ 26 := by
    have : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
    omega
  have h2 : (n + ((n + 1) ^ 26 + 2) + 1) ^ a.degree ≤ 4 ^ a.degree * (n + 1) ^ (26 * a.degree) := by
    calc _ ≤ (4 * (n + 1) ^ 26) ^ a.degree := Nat.pow_le_pow_left h1 _
      _ = 4 ^ a.degree * (n + 1) ^ (26 * a.degree) := by rw [mul_pow, ← pow_mul]
  have h3 : (n + 1) ^ (26 * a.degree) ≤ (n + 1) ^ (26 * a.degree + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : n + 2 ≤ 2 * (n + 1) ^ (26 * a.degree + 1) := by
    have : n + 1 ≤ (n + 1) ^ (26 * a.degree + 1) := Nat.le_self_pow (by omega) _
    omega
  have e : (a.coefficient * 4 ^ a.degree + 2) * (n + 1) ^ (26 * a.degree + 1) =
      a.coefficient * 4 ^ a.degree * (n + 1) ^ (26 * a.degree + 1) + 2 * (n + 1) ^ (26 * a.degree + 1) := by ring
  rw [e]
  have h5 : a.coefficient * (4 ^ a.degree * (n + 1) ^ (26 * a.degree)) ≤
      a.coefficient * 4 ^ a.degree * (n + 1) ^ (26 * a.degree + 1) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h3
  have h6 := Nat.mul_le_mul_left a.coefficient h2
  omega

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

