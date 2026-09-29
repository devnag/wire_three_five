import Proof.Wire_3_5.UnionMachine.FrontSemFold

/-! # C6 front, the semantic core (16): C1's carrier preparation is polynomial in the carrier's code (P3:3673)

**`carPre_le`**: the carrier-preparation fuel `carPreCost X 0 0` (C1's per-variable stage before its round) is at most
`CP·(W + 2)^{51}`, `W` the carrier code's bit length: `carTableCost_poly` argument restricted to the preparation's
stages (the atom count `≤ W`, the native region `≤ |X|·gateB W`, the envelope `value 50 cC2 (W+1)`, the power
table's `polyCoefficient`, base's traversal budget).

Paper quantity of the main type: the selection stage's per-carrier time. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCarPre
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.CarTable
open NearCubicWires.WireExponent3_5.PrimT.CarBounds NearCubicWires.WireExponent3_5.PrimT.CarFold

/-- The preparation's coefficient. -/
noncomputable def CP : ℕ := 10 ^ 31 + 4 * cC2 + BlockPlatform.UnaryCalc.polyCoefficient 50 cC2 + 16 * 10 ^ 18 + 1000

/-- **C1's carrier preparation fuel** is `≤ CP·(W+2)^{51}`. -/
theorem carPre_le {n : ℕ} (X : Stars.Carrier n) :
    C1CarPre.carPreCost X 0 0 ≤ CP * (natBitLength X.code + 2) ^ 51 := by
  have hcode : X.code < 2 ^ natBitLength X.code := CompilerMachine.Pool.lt_pow_natBitLength _
  have hW' : ∀ g ∈ X, CarrierFormat.gateCode g < 2 ^ natBitLength X.code := fun g hg =>
    SourceRequest.TermBridge.atom_lt (natBitLength X.code) X.code _ hcode
      (by rw [CarrierFormat.tree_atoms_code]; exact List.mem_map_of_mem hg)
  have htl := tabSeg_len_le (natBitLength X.code) X hW'
  have hc := (FrontSemGate.carrier_bits X).2
  have hpow := BlockPlatform.UnaryCalc.poly_cost_polyBounded 50 cC2 (natBitLength X.code + 1)
  unfold ValidatorPolynomialDomination.PolyBounded at hpow
  have hCT : CloseoutWitness.CanonicalTest.budget (binary (natBitLength X.code) X.code) =
      16 * 1000000000000000000 * (natBitLength X.code + 1) ^ 24 := by
    simp only [CloseoutWitness.CanonicalTest.budget, CloseoutWitness.Reencode.polynomialBudget, binary_length]
    ring
  have hT : BlockPlatform.UnaryCalc.value 50 cC2 (natBitLength X.code + 1) = cC2 * (natBitLength X.code + 2) ^ 50 :=
    value_eq _
  unfold C1CarPre.carPreCost
  simp only []
  rw [hCT, hT]
  generalize hWd : natBitLength X.code = W at *
  generalize hcd : X.length = c at *
  generalize htd : (tabSeg X).length = tl at *
  obtain ⟨M, hM⟩ : ∃ x, x = W + 2 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by omega
  have pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b := fun a b h => Nat.pow_le_pow_right hM1 h
  have p1 : M ≤ M ^ 51 := by have := pw 1 51 (by norm_num); simpa using this
  have p0 : 1 ≤ M ^ 51 := by have := pw 0 51 (by norm_num); simpa using this
  have hcM : c ≤ M := by omega
  have hG : gateB W ≤ 5000000000000000000000000 * M ^ 26 := by
    unfold gateB
    have := pw 1 26 (by norm_num); simp at this
    rw [← hM]
    omega
  have htlP : tl ≤ 5000000000000000000000000 * M ^ 27 := by
    have h2 : c * gateB W ≤ M * (5000000000000000000000000 * M ^ 26) := Nat.mul_le_mul hcM hG
    have e : M * (5000000000000000000000000 * M ^ 26) = 5000000000000000000000000 * M ^ 27 := by ring
    omega
  have hcw : foldCw W c tl ≤ 10 ^ 30 * M ^ 50 := by
    unfold foldCw
    have h1 : c * (5 * W + 8) ≤ M * (5 * M) := Nat.mul_le_mul hcM (by omega)
    have e1 : M * (5 * M) = 5 * M ^ 2 := by ring
    have h2 := pw 2 50 (by norm_num)
    have h26 := pw 26 50 (by norm_num)
    have h27 := pw 27 50 (by norm_num)
    have h1' := pw 1 50 (by norm_num); simp at h1'
    have hW26 : (W + 2) ^ 26 = M ^ 26 := by rw [hM]
    rw [hW26]
    omega
  have hin : foldCw W c tl + 1 + (2 * (cC2 * M ^ 50) + 4 + 1 + 0) + 2 ≤ (10 ^ 30 + 2 * cC2 + 8) * M ^ 50 := by
    have := pw 0 50 (by norm_num); simp at this
    have e : (10 ^ 30 + 2 * cC2 + 8) * M ^ 50 = 10 ^ 30 * M ^ 50 + 2 * (cC2 * M ^ 50) + 8 * M ^ 50 := by ring
    rw [e]; omega
  have hround : c * (foldCw W c tl + 1 + (2 * (cC2 * M ^ 50) + 4 + 1 + 0) + 2) ≤ (10 ^ 30 + 2 * cC2 + 8) * M ^ 51 := by
    calc c * _ ≤ M * ((10 ^ 30 + 2 * cC2 + 8) * M ^ 50) := Nat.mul_le_mul hcM hin
      _ = (10 ^ 30 + 2 * cC2 + 8) * M ^ 51 := by ring
  have hPB : PCPSerializerCapacity.Power.budget 50 cC2 (W + 1) ≤ BlockPlatform.UnaryCalc.polyCoefficient 50 cC2 * M ^ 51 := by
    refine hpow.trans (Nat.mul_le_mul_left _ ?_)
    rw [hM]
  have hCT' : 16 * 1000000000000000000 * (W + 1) ^ 24 ≤ 16 * 1000000000000000000 * M ^ 51 :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 24).trans (pw 24 51 (by norm_num)))
  have hT' : cC2 * M ^ 50 ≤ cC2 * M ^ 51 := Nat.mul_le_mul_left _ (pw 50 51 (by norm_num))
  have e2 : (W + 2) ^ 50 = M ^ 50 := by rw [hM]
  rw [e2]
  have hpre : prepCost W 0 0 ≤ 85 * M ^ 51 := by unfold prepCost; omega
  have eCP : CP * M ^ 51 = 10 ^ 31 * M ^ 51 + 4 * (cC2 * M ^ 51) +
      BlockPlatform.UnaryCalc.polyCoefficient 50 cC2 * M ^ 51 + 16 * 1000000000000000000 * M ^ 51 + 1000 * M ^ 51 := by
    unfold CP; ring
  have eR : (10 ^ 30 + 2 * cC2 + 8) * M ^ 51 = 10 ^ 30 * M ^ 51 + 2 * (cC2 * M ^ 51) + 8 * M ^ 51 := by ring
  rw [← hM, eCP]
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCarPre
