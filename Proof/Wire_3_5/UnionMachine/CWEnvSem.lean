import Proof.Wire_3_5.UnionMachine.CWEnvCode
import Proof.Wire_3_5.UnionMachine.CWSym

/-! # C6 front, U5, the code writers: the envelope machine decides `WithinEnvelope`

The envelope machine (`CWEnvCode.envCodeM`) reads a carrier's code; on the code of a carrier `X` of arity `q` its flag
is exactly the envelope bit of `X` (P3:3083-3094):
* the atoms' words are the gates' codes at the code's width (`CarrierFormat.tree_atoms_code`), each below
  `2^width` (base's `Reencode.atom_le`), so each word's gate fields are the gate's weights and threshold (`gate_codeWords`, `decode_weights`, `decode_threshold`): the fields decode (**`atoms_dec`**) and the word's bits are
  the gate's `encodingBits` (**`pbits_gate`**);
* **`flag_eq`**: the flag is `decide (X.length ≤ L ∧ ∀ g ∈ X, g.encodingBits ≤ L)`;
* **`envelope_step`**: at `L = (q+1)^deg` the output is the framed envelope bit, which is `X.WithinEnvelope deg`
  (**`envelope_iff`**).

Paper quantity of the main type: the envelope bit of a named carrier. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWEnvSem
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.CanonicalBinary
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvChk NearCubicWires.WireExponent3_5.UnionMachine.CWEnvRound
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvCode
open NearCubicWires.WireExponent3_5.PrimT.CarrierFormat (gateCode)

variable {q : ℕ}

/-- The atoms' words of a carrier's code are its gates' codes. -/
theorem atomsOf_code (X : Stars.Carrier q) :
    atomsOf X.code = X.map fun g => binary (natBitLength X.code) (gateCode g) := by
  unfold atomsOf; rw [PrimT.CarrierFormat.tree_atoms_code, List.map_map]; rfl

theorem gateCode_lt (X : Stars.Carrier q) (g : NormalizedThresholdGate q) (hg : g ∈ X) :
    gateCode g < 2 ^ natBitLength X.code := by
  have h1 : gateCode g ≤ X.code := CloseoutWitness.Reencode.atom_le _ _ (by
    rw [PrimT.CarrierFormat.tree_atoms_code]; exact List.mem_map_of_mem hg)
  have h2 : X.code < 2 ^ natBitLength X.code := Nat.lt_pow_succ_log_self (by norm_num) _
  omega

/-- The fields of a gate's code word. -/
theorem word_fields (W : ℕ) (g : NormalizedThresholdGate q) (hlt : gateCode g < 2 ^ W) :
    CanonicalBinary.decodeIntList (value (CWRoundB.cw (binary W (gateCode g)) 0)) = some (List.ofFn g.weight) ∧
      CanonicalBinary.decodeInt (value (CWRoundB.cw (binary W (gateCode g)) 1)) = some g.threshold := by
  obtain ⟨h0, h1, -⟩ := PrimT.CarrierFormat.gate_codeWords g _ (binary_value _ _ hlt)
  exact ⟨by rw [CWRoundB.cw, h0]; exact PrimT.CarrierFormat.decode_weights g,
    by rw [CWRoundB.cw, h1]; exact PrimT.CarrierFormat.decode_threshold g⟩

/-- **Every atom word's fields decode.** -/
theorem atoms_dec (X : Stars.Carrier q) : ∀ y ∈ atomsOf X.code, Dec y := by
  intro y hy
  rw [atomsOf_code] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
  obtain ⟨h0, h1⟩ := word_fields _ g (gateCode_lt X g hg)
  exact ⟨by rw [h0]; rfl, by rw [h1]; rfl⟩

theorem wbits_ofFn (w : Fin q → ℤ) : wbits (List.ofFn w) = ∑ i, intBitLength (w i) := by
  unfold wbits
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- **A gate word's bits are the gate's description bits.** -/
theorem pbits_gate (W : ℕ) (g : NormalizedThresholdGate q) (hlt : gateCode g < 2 ^ W) :
    pbits (binary W (gateCode g)) = g.encodingBits := by
  obtain ⟨h0, h1⟩ := word_fields W g hlt
  unfold pbits wsOf thOf
  rw [h0, h1]
  simp only [Option.getD_some]
  rw [wbits_ofFn]
  unfold NormalizedThresholdGate.encodingBits
  have e : natBitLength g.threshold.natAbs = intBitLength g.threshold := rfl
  rw [e]; ring

/-- **The flag is the envelope decision at `L`.** -/
theorem flag_eq (X : Stars.Carrier q) (L : ℕ) :
    (decide ((atomsOf X.code).length ≤ L) && (atomsOf X.code).all fun y => decide (pbits y ≤ L)) =
      decide (X.length ≤ L ∧ ∀ g ∈ X, g.encodingBits ≤ L) := by
  have hall : ((atomsOf X.code).all fun y => decide (pbits y ≤ L)) = decide (∀ g ∈ X, g.encodingBits ≤ L) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff, atomsOf_code]
    constructor
    · intro h g hg
      have := h _ (List.mem_map_of_mem hg)
      rw [pbits_gate _ g (gateCode_lt X g hg)] at this
      simpa using this
    · intro h y hy
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
      rw [pbits_gate _ g (gateCode_lt X g hg)]
      simpa using h g hg
  rw [hall, atomsOf_code, List.length_map]
  simp [Bool.decide_and]

/-- The envelope bit at `L = (q+1)^deg` is `WithinEnvelope`. -/
theorem envelope_iff (X : Stars.Carrier q) (deg : ℕ) :
    decide (X.length ≤ (q + 1) ^ deg ∧ ∀ g ∈ X, g.encodingBits ≤ (q + 1) ^ deg) = true ↔ X.WithinEnvelope deg := by
  rw [decide_eq_true_iff]; rfl

/-- **The envelope machine on a carrier's code** at `L = (q+1)^deg`: the output is the carrier's envelope bit
(`envelope_iff`). -/
theorem envelope_step (X : Stars.Carrier q) (deg T : ℕ)
    (hc : (atomsOf X.code).length ≤ T) (hS : ((atomsOf X.code).flatMap frame).length ≤ T) (hLT : (q + 1) ^ deg ≤ T)
    (hcw : foldCwE (natBitLength X.code) (atomsOf X.code).length + 1 ≤ T) :
    ∃ out : Fin 1192 → List Bool,
      Step envCodeM (envCodeCost X.code T) (fun _ => 0) (envCodeIn X.code ((q + 1) ^ deg) T) (fun _ => 0) out ∧
      out 0 = frame (natWord X.code) ∧ out 1 = List.replicate ((q + 1) ^ deg) true ∧
      out 1189 = List.replicate T true ∧
      out 2 = frame [decide (X.length ≤ (q + 1) ^ deg ∧ ∀ g ∈ X, g.encodingBits ≤ (q + 1) ^ deg)] := by
  obtain ⟨out, st, h0, h1, h2, h3⟩ := envCode_step X.code ((q + 1) ^ deg) T (Nat.one_le_pow _ _ (by omega))
    (atoms_dec X) hc hS hLT hcw
  exact ⟨out, st, h0, h1, h2, by rw [h3, flag_eq]⟩

end NearCubicWires.WireExponent3_5.UnionMachine.CWEnvSem
