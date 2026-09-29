import Proof.Wire_3_5.Primitive.SeedFix.CarTable
import Proof.Wire_3_5.Primitive.SeedFix.TabCost

/-! # The carrier table: polynomial fuel (P3:3049-3050, 3071-3076)

"One-sided scores may be computed directly at a sampled row in polynomial time" (P3:3049-3050). The carrier table's
fuel `carTableCost X L` is polynomial in the code's bit length `W`, the arity `n`, and the description bound `L`
(**`carTableCost_poly`**, in base's `PolyBounded` form, degree 76). The atom count `|X|` and the native region
`tabH X` enter through the machine-derived bounds that also size the loop's bank:
* the traversal's budget bounds the atom count (`carCount_le`);
* base's per-atom worker bounds every native word (`CarTable.gate_len_le`).

Paper quantity of the main type: the carrier table's running time. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.CarCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.CarTable
open NearCubicWires.WireExponent3_5.PrimT.CarBounds NearCubicWires.WireExponent3_5.PrimT.CarFold
open NearCubicWires.WireExponent3_5.PrimT.CarStages NearCubicWires.WireExponent3_5.PrimT.CarMask
open NearCubicWires.WireExponent3_5.Transfer

/-- **The atom count is bounded by base's traversal budget.** -/
theorem carCount_le {n : ℕ} (X : Stars.Carrier n) :
    X.length * (2 * natBitLength X.code + 1) ≤
      max (2 * natBitLength X.code + 1) (16 * 1000000000000000000 * (natBitLength X.code + 1) ^ 24 + 1) := by
  set W := natBitLength X.code with hW
  set bits := binary W X.code with hbits
  have hval : RadixSemantics.value bits = X.code := binary_value _ _ (CompilerMachine.Pool.lt_pow_natBitLength _)
  obtain ⟨o3, r3, t30, -, -⟩ := CloseoutWitness.CanonicalTest.fields_run bits
  have hl := ready_lengths r3 (2 * W + 1) (fun i => by
    show (if i.val = 0 then frame bits else []).length ≤ _
    split_ifs
    · rw [frame_length, hbits, binary_length]
    · simp) 30
  rw [t30, binary_length, hval, stream_eq W X, rawAtoms_len] at hl
  have hb : CloseoutWitness.CanonicalTest.budget bits = 16 * 1000000000000000000 * (W + 1) ^ 24 := by
    simp only [CloseoutWitness.CanonicalTest.budget, CloseoutWitness.Reencode.polynomialBudget, hbits, binary_length]
    ring
  rw [hb] at hl
  exact hl

/-- **The carrier table's fuel is polynomial** in the code's bit length, the arity and the description bound. -/
theorem carTableCost_poly {n : ℕ} (X : Stars.Carrier n) (L : ℕ)
    (h2 : 2 ≤ n + L) :
    PolyBounded (carTableCost X L) (natBitLength X.code + n + L)
      (10 ^ 160 + 16 * 1000000000000000000 + BlockPlatform.UnaryCalc.polyCoefficient 50 cC2) 76 := by
  set W := natBitLength X.code with hW
  set c := X.length with hc
  set tl := (tabSeg X).length with htl
  set M := W + n + L + 1 with hM
  have hWM : W + 2 ≤ M := by omega
  have hM1 : 1 ≤ M := by omega
  have hnM : n ≤ M := by omega
  clear_value M
  have hcodeW : X.code < 2 ^ W := CompilerMachine.Pool.lt_pow_natBitLength _
  have hW' : ∀ g ∈ X, CarrierFormat.gateCode g < 2 ^ W := fun g hg =>
    SourceRequest.TermBridge.atom_lt W X.code _ hcodeW (by rw [CarrierFormat.tree_atoms_code]; exact List.mem_map_of_mem hg)
  -- the powers of `M`
  have pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b := fun a b h => Nat.pow_le_pow_right hM1 h
  have e2450 : M ^ 24 * M ^ 50 = M ^ 74 := by rw [← pow_add]
  have e2451 : M ^ 24 * M ^ 51 = M ^ 75 := by rw [← pow_add]
  have e2426 : M ^ 24 * M ^ 26 = M ^ 50 := by rw [← pow_add]
  have e150 : M * M ^ 50 = M ^ 51 := by ring
  have hM24 : (W + 2) ^ 24 ≤ M ^ 24 := Nat.pow_le_pow_left hWM _
  have hM26 : (W + 2) ^ 26 ≤ M ^ 26 := Nat.pow_le_pow_left hWM _
  have hM50 : (W + 2) ^ 50 ≤ M ^ 50 := Nat.pow_le_pow_left hWM _
  have hW1 : (W + 1) ^ 24 ≤ M ^ 24 := Nat.pow_le_pow_left (by omega) _
  have hWp : W + 2 ≤ M ^ 24 := hWM.trans (by simpa using pw 1 24 (by norm_num))
  -- the atom count
  have hcP : c ≤ 17000000000000000000 * M ^ 24 := by
    have hcnt := carCount_le X
    rw [← hW, ← hc] at hcnt
    rcases le_max_iff.mp hcnt with h | h
    · have : c ≤ 1 := by
        by_contra hc1
        have : 2 * (2 * W + 1) ≤ c * (2 * W + 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      have := pw 0 24 (by norm_num); simp at this; omega
    · have : c ≤ c * (2 * W + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  -- the native region
  have hG : gateB W ≤ 5000000000000000000000000 * M ^ 26 := by
    unfold gateB
    have := pw 1 26 (by norm_num); simp at this
    omega
  have htlP : tl ≤ 17000000000000000000 * 5000000000000000000000000 * M ^ 50 := by
    have h1 := tabSeg_len_le W X hW'
    rw [← hc, ← htl] at h1
    have h2 : c * gateB W ≤ (17000000000000000000 * M ^ 24) * (5000000000000000000000000 * M ^ 26) :=
      Nat.mul_le_mul hcP hG
    have e : (17000000000000000000 * M ^ 24) * (5000000000000000000000000 * M ^ 26) =
        17000000000000000000 * 5000000000000000000000000 * (M ^ 24 * M ^ 26) := by ring
    rw [e, e2426] at h2
    omega
  -- the capacity
  have hT : BlockPlatform.UnaryCalc.value 50 cC2 (W + 1) ≤ cC2 * M ^ 50 := by
    rw [value_eq]; exact Nat.mul_le_mul_left _ hM50
  -- the loop's round
  have hcw : foldCw W c tl ≤ 10 ^ 47 * M ^ 50 := by
    unfold foldCw
    have hcW : c * W ≤ 17000000000000000000 * M ^ 50 := by
      have := Nat.mul_le_mul hcP (show W ≤ M ^ 26 by have := pw 1 26 (by norm_num); simp at this; omega)
      have e : 17000000000000000000 * M ^ 24 * M ^ 26 = 17000000000000000000 * M ^ 50 := by
        rw [Nat.mul_assoc, e2426]
      omega
    have e1 : c * (5 * W + 8) = 5 * (c * W) + 8 * c := by ring
    have h26 := pw 26 50 (by norm_num)
    have h24 := pw 24 50 (by norm_num)
    have hWc : 4000000000000000000001002 * (W + 2) ^ 26 ≤ 4000000000000000000001002 * M ^ 50 :=
      Nat.mul_le_mul_left _ (hM26.trans h26)
    rw [e1]
    omega
  have hround : c * (foldCw W c tl + 1 + (2 * BlockPlatform.UnaryCalc.value 50 cC2 (W + 1) + 4 + 1 + 0) + 2) ≤
      17000000000000000000 * (10 ^ 47 + 2 * cC2 + 8) * M ^ 74 := by
    have hin : foldCw W c tl + 1 + (2 * BlockPlatform.UnaryCalc.value 50 cC2 (W + 1) + 4 + 1 + 0) + 2 ≤
        (10 ^ 47 + 2 * cC2 + 8) * M ^ 50 := by
      have := pw 0 50 (by norm_num); simp at this
      have e : (10 ^ 47 + 2 * cC2 + 8) * M ^ 50 = 10 ^ 47 * M ^ 50 + 2 * (cC2 * M ^ 50) + 8 * M ^ 50 := by ring
      rw [e]; omega
    calc c * _ ≤ (17000000000000000000 * M ^ 24) * ((10 ^ 47 + 2 * cC2 + 8) * M ^ 50) := Nat.mul_le_mul hcP hin
      _ = 17000000000000000000 * (10 ^ 47 + 2 * cC2 + 8) * (M ^ 24 * M ^ 50) := by ring
      _ = _ := by rw [e2450]
  -- the mask stage
  have hnh : n * tl ≤ 17000000000000000000 * 5000000000000000000000000 * M ^ 51 := by
    have := Nat.mul_le_mul hnM htlP
    have e : M * (17000000000000000000 * 5000000000000000000000000 * M ^ 50) =
        17000000000000000000 * 5000000000000000000000000 * (M * M ^ 50) := by ring
    rw [e, e150] at this; exact this
  have hmask : c * (maskCost n tl + 2) ≤ 17000000000000000000 * 10 ^ 50 * M ^ 75 := by
    have hin : maskCost n tl + 2 ≤ 10 ^ 50 * M ^ 51 := by
      unfold maskCost gateCost gateACost gateBCost
      have e1 : 16 * n * tl = 16 * (n * tl) := by ring
      have e2 : 70 * n * tl = 70 * (n * tl) := by ring
      rw [e1, e2]
      have h50 := pw 50 51 (by norm_num)
      have h1 := pw 1 51 (by norm_num); simp at h1
      have h0 := pw 0 51 (by norm_num); simp at h0
      have htl51 : tl ≤ 17000000000000000000 * 5000000000000000000000000 * M ^ 51 :=
        htlP.trans (Nat.mul_le_mul_left _ h50)
      omega
    calc c * _ ≤ (17000000000000000000 * M ^ 24) * (10 ^ 50 * M ^ 51) := Nat.mul_le_mul hcP hin
      _ = 17000000000000000000 * 10 ^ 50 * (M ^ 24 * M ^ 51) := by ring
      _ = _ := by rw [e2451]
  -- the rest
  have hpow := (BlockPlatform.UnaryCalc.poly_cost_polyBounded 50 cC2 (W + 1))
  unfold PolyBounded at hpow
  have hpow' : PCPSerializerCapacity.Power.budget 50 cC2 (W + 1) ≤
      BlockPlatform.UnaryCalc.polyCoefficient 50 cC2 * M ^ 76 := by
    refine hpow.trans (Nat.mul_le_mul_left _ ?_)
    exact (Nat.pow_le_pow_left (by omega) _).trans (pw 51 76 (by norm_num))
  have hCT : CloseoutWitness.CanonicalTest.budget (binary W X.code) ≤ 16 * 1000000000000000000 * M ^ 76 := by
    simp only [CloseoutWitness.CanonicalTest.budget, CloseoutWitness.Reencode.polynomialBudget, binary_length]
    have := hW1.trans (pw 24 76 (by norm_num))
    have e : 16 * (1000000000000000000 * (W + 1) ^ 24) = 16 * 1000000000000000000 * (W + 1) ^ 24 := by ring
    rw [e]; exact Nat.mul_le_mul_left _ this
  have h74 := pw 74 76 (by norm_num)
  have h75 := pw 75 76 (by norm_num)
  have h50 := pw 50 76 (by norm_num)
  have h1 := pw 1 76 (by norm_num); simp at h1
  have h0 := pw 0 76 (by norm_num); simp at h0
  have hTT := hT.trans (Nat.mul_le_mul_left _ h50)
  have htl76 := htlP.trans (Nat.mul_le_mul_left _ h50)
  have hc76 : c ≤ 17000000000000000000 * M ^ 76 := hcP.trans (Nat.mul_le_mul_left _ (pw 24 76 (by norm_num)))
  have hr76 := hround.trans (Nat.mul_le_mul_left _ h74)
  have hm76 := hmask.trans (Nat.mul_le_mul_left _ h75)
  unfold PolyBounded carTableCost
  simp only []
  rw [← hW, ← hM]
  unfold mskCost scanCost prepCost tabH
  have hnbl0 : natBitLength 0 = 1 := rfl
  rw [hnbl0, ← hc, ← htl]
  simp only [List.length_nil]
  have eK : (10 ^ 160 + 16 * 1000000000000000000 + BlockPlatform.UnaryCalc.polyCoefficient 50 cC2) * M ^ 76 =
      10 ^ 160 * M ^ 76 + 16 * 1000000000000000000 * M ^ 76 + BlockPlatform.UnaryCalc.polyCoefficient 50 cC2 * M ^ 76 := by
    ring
  refine le_trans ?_ (le_of_eq eK.symm)
  have hbig1 : 17000000000000000000 * (10 ^ 47 + 2 * cC2 + 8) * M ^ 76 +
      17000000000000000000 * 10 ^ 50 * M ^ 76 * 2 + cC2 * M ^ 76 * 4 +
      17000000000000000000 * 5000000000000000000000000 * M ^ 76 * 200 +
      17000000000000000000 * M ^ 76 * 20 + 1000 * M ^ 76 ≤ 10 ^ 160 * M ^ 76 := by
    have e : 17000000000000000000 * (10 ^ 47 + 2 * cC2 + 8) * M ^ 76 +
        17000000000000000000 * 10 ^ 50 * M ^ 76 * 2 + cC2 * M ^ 76 * 4 +
        17000000000000000000 * 5000000000000000000000000 * M ^ 76 * 200 +
        17000000000000000000 * M ^ 76 * 20 + 1000 * M ^ 76 =
        (17000000000000000000 * (10 ^ 47 + 2 * cC2 + 8) + 17000000000000000000 * 10 ^ 50 * 2 + cC2 * 4 +
          17000000000000000000 * 5000000000000000000000000 * 200 + 17000000000000000000 * 20 + 1000) * M ^ 76 := by
      ring
    rw [e]
    exact Nat.mul_le_mul_right _ (by norm_num [cC2])
  omega

end NearCubicWires.WireExponent3_5.PrimT.CarCost
