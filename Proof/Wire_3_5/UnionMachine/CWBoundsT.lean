import Proof.Wire_3_5.UnionMachine.CWMainT
import Proof.Wire_3_5.UnionMachine.CWBounds

/-! # C6 front, U5, the code writers: the `THR∘THR` core's capacity and time are polynomial

The same bounds as FP's `CWBounds` for the `THR∘THR` core (`CWMainT.coreTM`), for every list `xs` of codes whose
selectors match their bottoms (`hsel`, true of every `THR∘THR` circuit code):
* the retained bottoms are a sublist of all bottoms, so they are at most `n`, each of width `≤ n`;
* **`capsT_ok`**: FP's capacity `T = C₀·(n+1)^24` dominates the `THR∘THR` loops' needs (`CWMainT.CapsT`);
* **`coreTCost_le`**: the core's fuel is at most FP's `Kc·(n+1)^26`.

Paper quantity: the writer's time bound, a fixed polynomial in the input length. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWBoundsT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords NearCubicWires.WireExponent3_5.UnionMachine.CWCore
open NearCubicWires.WireExponent3_5.UnionMachine.CWMain (C0 cap)
open NearCubicWires.WireExponent3_5.UnionMachine.CWMainT
open NearCubicWires.WireExponent3_5.UnionMachine.CWBounds (u_len len_le nbl_le bots_len flat_le gc_bits_le le_cap Kc mass_eq)

/-! ## Sizes of the retained bottoms -/

theorem botsT_sub (xs : List ℕ) (hsel : ∀ x ∈ xs, (CWRoundT.sels x).length = (CWRoundA.bw x).length) :
    List.Sublist (botsT xs) (CWMainT.bots xs) :=
  CWRoundT.bacT_sub xs hsel xs.length

theorem botsT_len (xs : List ℕ) (hsel : ∀ x ∈ xs, (CWRoundT.sels x).length = (CWRoundA.bw x).length) :
    (botsT xs).length ≤ ((xs.map natWord).flatten).length :=
  (botsT_sub xs hsel).length_le.trans (bots_len xs)

theorem botsT_width (xs : List ℕ) (hsel : ∀ x ∈ xs, (CWRoundT.sels x).length = (CWRoundA.bw x).length) :
    ∀ y ∈ botsT xs, y.length ≤ ((xs.map natWord).flatten).length :=
  fun y hy => CWBounds.bots_width xs y ((botsT_sub xs hsel).subset hy)

theorem codesT_eq (xs : List ℕ) : codesT xs = (botsT xs).map fun y => (CWRoundB.gc y).bits := by
  simp [codesT, CWRoundB.gacc]

theorem codesT_width (xs : List ℕ) (hsel : ∀ x ∈ xs, (CWRoundT.sels x).length = (CWRoundA.bw x).length) :
    ∀ g ∈ codesT xs, g.length ≤ 20 * ((xs.map natWord).flatten).length + 40 := by
  intro g hg
  rw [codesT_eq] at hg
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hg
  have := gc_bits_le y
  have := botsT_width xs hsel y hy
  omega

theorem codesT_len (xs : List ℕ) : (codesT xs).length = (botsT xs).length := by
  rw [codesT_eq, List.length_map]

/-! ## The capacity -/

/-- **The capacity dominates the loops' needs.** -/
theorem capsT_ok (xs : List ℕ) (hsel : ∀ x ∈ xs, (CWRoundT.sels x).length = (CWRoundA.bw x).length) :
    CapsT xs (cap ((xs.map natWord).flatten).length) := by
  set n := ((xs.map natWord).flatten).length with hn
  have hc : xs.length ≤ n := len_le xs
  have hN : (bots xs).length ≤ n := bots_len xs
  have hNT : (botsT xs).length ≤ n := botsT_len xs hsel
  have hB : ((bots xs).flatMap frame).length ≤ n * (2 * n + 1) :=
    (flat_le _ n (CWBounds.bots_width xs)).trans (Nat.mul_le_mul_right _ hN)
  have hG : ((codesT xs).flatMap frame).length ≤ n * (2 * (20 * n + 40) + 1) := by
    have := flat_le _ (20 * n + 40) (codesT_width xs hsel)
    rw [codesT_len] at this
    exact this.trans (Nat.mul_le_mul_right _ hNT)
  have hS : ((xs.map nf).flatten ++ [false]).length = 2 * n + 1 := by
    rw [← frame_fields, frame_eq_frameP]; simp [hn]
  have hQ : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have hQP : (n + 1) ^ 2 ≤ (n + 1) ^ 24 := Nat.pow_le_pow_right (by omega) (by omega)
  have hBQ : ((bots xs).flatMap frame).length ≤ 2 * (n + 1) ^ 2 := by nlinarith
  have hGQ : ((codesT xs).flatMap frame).length ≤ 81 * (n + 1) ^ 2 := by nlinarith
  have hcA : xs.length * (18 * n + 16) ≤ 18 * (n + 1) ^ 2 := by
    have := Nat.mul_le_mul_right (18 * n + 16) hc; nlinarith
  have hcB : (botsT xs).length * (5 * n + 8) ≤ 5 * (n + 1) ^ 2 + 3 * (n + 1) := by
    have := Nat.mul_le_mul_right (5 * n + 8) hNT; nlinarith
  have hWN : (6 * n + 33) * (bots xs).length ≤ 39 * (n + 1) ^ 2 := by
    have := Nat.mul_le_mul_left (6 * n + 33) hN; nlinarith
  have e1 : (2 * n + 4) ^ 2 ≤ 16 * (n + 1) ^ 2 := by nlinarith
  have e2 : (5 * n + 9) ^ 2 ≤ 81 * (n + 1) ^ 2 := by nlinarith
  have e3 : (10 * n + 20) ^ 2 ≤ 400 * (n + 1) ^ 2 := by nlinarith
  have hn1 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hA : CWRoundT.foldCwT n xs.length ((bots xs).flatMap frame).length (bots xs).length + 1 ≤ cap n := by
    apply le_cap n _ (32 * 1000000000000000000 + 1000000) _ (by unfold C0; norm_num)
    unfold CWRoundT.foldCwT
    generalize (n + 1) ^ 24 = P at *
    generalize (n + 1) ^ 2 = Q at *
    generalize (6 * n + 33) * (bots xs).length = z at *
    omega
  have hBB : CWRoundB.foldCwB n (botsT xs).length ((codesT xs).flatMap frame).length + 1 ≤ cap n := by
    apply le_cap n _ 1000000 _ (by unfold C0; norm_num)
    unfold CWRoundB.foldCwB
    generalize (n + 1) ^ 24 = P at *
    generalize (n + 1) ^ 2 = Q at *
    generalize (2 * n + 4) ^ 2 = Q1 at *
    generalize (5 * n + 9) ^ 2 = Q2 at *
    generalize (10 * n + 20) ^ 2 = Q3 at *
    omega
  refine ⟨nbl_le xs, botsT_width xs hsel, ?_, ?_, ?_, ?_, hA, ?_, hBB⟩
  · apply le_cap n _ 1 _ (by unfold C0; norm_num)
    generalize (n + 1) ^ 24 = P at *; generalize (n + 1) ^ 2 = Q at *; omega
  · rw [hS]; apply le_cap n _ 2 _ (by unfold C0; norm_num)
    generalize (n + 1) ^ 24 = P at *; generalize (n + 1) ^ 2 = Q at *; omega
  · apply le_cap n _ 2 _ (by unfold C0; norm_num)
    generalize (n + 1) ^ 24 = P at *; generalize (n + 1) ^ 2 = Q at *; omega
  · apply le_cap n _ 1 _ (by unfold C0; norm_num)
    generalize (n + 1) ^ 24 = P at *; generalize (n + 1) ^ 2 = Q at *; omega
  · apply le_cap n _ 81 _ (by unfold C0; norm_num)
    generalize (n + 1) ^ 24 = P at *; generalize (n + 1) ^ 2 = Q at *; omega

/-! ## The time -/

/-- The core's fuel as a function of its ingredients. -/
def costFT (n c N PB T XA XB SC NC : ℕ) : ℕ :=
  1 + 1 + ((2 * (n * 9 + 1) + 2) + 1 + ((2 * (c * (18 * n + 16) + 5) + 2) + 1 +
    (PB + 1 + ((2 * 3 + 2) + 1 + ((2 * T + 4) + 1 +
      ((1 + 1 + (c * (XA + 1 + (2 * T + 4 + 1 + 0) + 2) + c + 3 + 1 + 1)) + 1 + ((2 * T + 4) + 1 +
      ((1 + 1 + (N * (XB + 1 + (2 * T + 4 + 1 + 0) + 2) + N + 3 + 1 + 1)) + 1 +
      (SC + 1 + (2 * NC + 2))))))))))

theorem coreTCost_eq (xs : List ℕ) : coreTCost xs = costFT ((xs.map natWord).flatten).length xs.length (botsT xs).length
    (PCPSerializerCapacity.Power.budget 24 C0 ((xs.map natWord).flatten).length) (cap ((xs.map natWord).flatten).length)
    (CWRoundT.foldCwT ((xs.map natWord).flatten).length xs.length ((bots xs).flatMap frame).length (bots xs).length)
    (CWRoundB.foldCwB ((xs.map natWord).flatten).length (botsT xs).length ((codesT xs).flatMap frame).length)
    (serCost (codesT xs)) (natCost (PCPTraversal.code (codesT xs))) := rfl

/-- **The `THR∘THR` core's time is a fixed polynomial**: `coreTCost xs ≤ Kc·(|u|+1)^26`. -/
theorem coreTCost_le (xs : List ℕ) (hsel : ∀ x ∈ xs, (CWRoundT.sels x).length = (CWRoundA.bw x).length) :
    coreTCost xs ≤ Kc * (((xs.map natWord).flatten).length + 1) ^ 26 := by
  have hc := capsT_ok xs hsel
  set n := ((xs.map natWord).flatten).length with hn
  have hcx : xs.length ≤ n := len_le xs
  have hN : (botsT xs).length ≤ n := botsT_len xs hsel
  have hG : ((codesT xs).flatMap frame).length ≤ n * (2 * (20 * n + 40) + 1) := by
    have := flat_le _ (20 * n + 40) (codesT_width xs hsel)
    rw [codesT_len] at this
    exact this.trans (Nat.mul_le_mul_right _ hN)
  set m := n + 1 with hm
  have hQ : m ^ 2 = n * n + 2 * n + 1 := by rw [hm]; ring
  have p24 : m ^ 24 ≤ m ^ 25 := Nat.pow_le_pow_right (by omega) (by omega)
  have p25 : m ^ 25 ≤ m ^ 26 := Nat.pow_le_pow_right (by omega) (by omega)
  have p2 : m ^ 2 ≤ m ^ 24 := Nat.pow_le_pow_right (by omega) (by omega)
  have p10 : m ^ 10 ≤ m ^ 24 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : m ≤ m ^ 2 := by nlinarith
  have hnP : n * m ^ 24 ≤ m ^ 25 := by
    calc n * m ^ 24 ≤ m * m ^ 24 := Nat.mul_le_mul_right _ (by omega)
      _ = m ^ 25 := by ring
  have hT : cap n = C0 * m ^ 24 := by unfold cap BlockPlatform.UnaryCalc.value; rw [hm]
  -- the serializer's mass
  set M := PCPSerializerMass.mass (codesT xs) with hM
  have hMb : M + 1 ≤ 82 * m ^ 2 := by rw [hM, mass_eq]; nlinarith
  have hM12 : (M + 1) ^ 12 ≤ 82 ^ 12 * m ^ 24 := by
    calc (M + 1) ^ 12 ≤ (82 * m ^ 2) ^ 12 := Nat.pow_le_pow_left hMb _
      _ = 82 ^ 12 * m ^ 24 := by rw [mul_pow, ← pow_mul]
  have hM5 : (M + 1) ^ 5 ≤ 82 ^ 5 * m ^ 10 := by
    calc (M + 1) ^ 5 ≤ (82 * m ^ 2) ^ 5 := Nat.pow_le_pow_left hMb _
      _ = 82 ^ 5 * m ^ 10 := by rw [mul_pow, ← pow_mul]
  have hbits : (PCPTraversal.code (codesT xs)).bits.length ≤ 3 * (M + 1) ^ 5 := PCPSerializerMass.code_bits _
  have hpoly := BlockPlatform.UnaryCalc.poly_cost_polyBounded 24 C0 n
  unfold ValidatorPolynomialDomination.PolyBounded at hpoly
  have hcA : xs.length * (18 * n + 16) ≤ 18 * m ^ 2 := by
    have := Nat.mul_le_mul_right (18 * n + 16) hcx; nlinarith
  -- the loops
  have hA7 : xs.length * (CWRoundT.foldCwT n xs.length ((bots xs).flatMap frame).length (bots xs).length + 1 +
      (2 * cap n + 4 + 1 + 0) + 2) ≤ 3 * C0 * m ^ 25 + 7 * n := by
    have h1 := Nat.mul_le_mul_right (3 * cap n + 7) hcx
    have h2 : CWRoundT.foldCwT n xs.length ((bots xs).flatMap frame).length (bots xs).length + 1 +
      (2 * cap n + 4 + 1 + 0) + 2 ≤ 3 * cap n + 7 := by have := hc.a5; rw [← hn] at this; omega
    have h3 := Nat.mul_le_mul_left xs.length h2
    have h4 : n * (3 * cap n + 7) = 3 * C0 * (n * m ^ 24) + 7 * n := by rw [hT]; ring
    have h5 := Nat.mul_le_mul_left (3 * C0) hnP
    omega
  have hA9 : (botsT xs).length * (CWRoundB.foldCwB n (botsT xs).length ((codesT xs).flatMap frame).length + 1 +
      (2 * cap n + 4 + 1 + 0) + 2) ≤ 3 * C0 * m ^ 25 + 7 * n := by
    have h1 := Nat.mul_le_mul_right (3 * cap n + 7) hN
    have h2 : CWRoundB.foldCwB n (botsT xs).length ((codesT xs).flatMap frame).length + 1 +
      (2 * cap n + 4 + 1 + 0) + 2 ≤ 3 * cap n + 7 := by have := hc.b4; rw [← hn] at this; omega
    have h3 := Nat.mul_le_mul_left (botsT xs).length h2
    have h4 : n * (3 * cap n + 7) = 3 * C0 * (n * m ^ 24) + 7 * n := by rw [hT]; ring
    have h5 := Nat.mul_le_mul_left (3 * C0) hnP
    omega
  rw [coreTCost_eq, ← hn]
  unfold costFT serCost natCost PCPTraversal.budget
  rw [← hM, hT]
  have hpoly' : PCPSerializerCapacity.Power.budget 24 C0 n ≤ BlockPlatform.UnaryCalc.polyCoefficient 24 C0 * m ^ 25 :=
    hpoly
  have hsum : Kc * m ^ 26 = BlockPlatform.UnaryCalc.polyCoefficient 24 C0 * m ^ 26 + 20 * C0 * m ^ 26 +
      2 * 1000000000000 * 82 ^ 12 * m ^ 26 + 1000 * 82 ^ 5 * m ^ 26 + 1000 * m ^ 26 := by unfold Kc; ring
  rw [hsum]
  have q1 := Nat.mul_le_mul_left (BlockPlatform.UnaryCalc.polyCoefficient 24 C0) p25
  have q2 : C0 * m ^ 24 ≤ C0 * m ^ 26 := Nat.mul_le_mul_left _ (p24.trans p25)
  have q3 : C0 * m ^ 25 ≤ C0 * m ^ 26 := Nat.mul_le_mul_left _ p25
  have q4 : 1000000000000 * (M + 1) ^ 12 ≤ 1000000000000 * 82 ^ 12 * m ^ 26 := by
    have h1 := Nat.mul_le_mul_left 1000000000000 hM12
    have h2 : 1000000000000 * (82 ^ 12 * m ^ 24) ≤ 1000000000000 * (82 ^ 12 * m ^ 26) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (p24.trans p25))
    calc 1000000000000 * (M + 1) ^ 12 ≤ 1000000000000 * (82 ^ 12 * m ^ 26) := h1.trans h2
      _ = 1000000000000 * 82 ^ 12 * m ^ 26 := by ring
  have q5 : (PCPTraversal.code (codesT xs)).bits.length ≤ 3 * 82 ^ 5 * m ^ 26 := by
    have h1 : 3 * (M + 1) ^ 5 ≤ 3 * (82 ^ 5 * m ^ 26) :=
      Nat.mul_le_mul_left _ (hM5.trans (Nat.mul_le_mul_left _ (p10.trans (p24.trans p25))))
    calc (PCPTraversal.code (codesT xs)).bits.length ≤ 3 * (82 ^ 5 * m ^ 26) := hbits.trans h1
      _ = 3 * 82 ^ 5 * m ^ 26 := by ring
  have q6 : m ≤ m ^ 26 := p1.trans (p2.trans (p24.trans p25))
  have q7 : m ^ 2 ≤ m ^ 26 := p2.trans (p24.trans p25)
  have q8 : 1 ≤ m ^ 26 := le_trans (by omega) q6
  have hc1 : 20 * C0 * m ^ 26 = 20 * (C0 * m ^ 26) := by ring
  have hc2 : 2 * 1000000000000 * 82 ^ 12 * m ^ 26 = 2 * (1000000000000 * 82 ^ 12 * m ^ 26) := by ring
  have hc3 : 1000 * 82 ^ 5 * m ^ 26 = 1000 * (82 ^ 5 * m ^ 26) := by ring
  have hc4 : 3 * 82 ^ 5 * m ^ 26 = 3 * (82 ^ 5 * m ^ 26) := by ring
  rw [hc1, hc2, hc3]
  rw [hc4] at q5
  have h3C : 3 * C0 * m ^ 25 = 3 * (C0 * m ^ 25) := by ring
  have hA7' := hA7
  have hA9' := hA9
  rw [hT, h3C] at hA7' hA9'
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.CWBoundsT
