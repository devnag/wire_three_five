import Proof.Wire_3_5.UnionMachine.CWMain

/-! # C6 front, U5, the code writers: the core's capacity and time are polynomial

The union front runs each writer "in polynomial time" (the weak machine's budget, P3:3669-3674; the writers' interface
asks for `K·(|u| + q + 1)^d`). This module proves, for every list `xs` of codes with `u = (xs.map natWord).flatten`,
`n = |u|`:
* the size facts: `xs.length ≤ n`, every code has `natBitLength ≤ n`, at most `n` bottoms, each of width `≤ n`, each atom
  code of at most `20n + 40` bits;
* **`caps_ok`**: the capacity `T = C₀·(n+1)^24` dominates the loops' needs (`CWMain.Caps`);
* **`coreCost_le`**: the core's fuel is at most `K·(n+1)^30`.

Paper quantity: the writer's time bound, a fixed polynomial in the input length. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords NearCubicWires.WireExponent3_5.UnionMachine.CWCore
open NearCubicWires.WireExponent3_5.UnionMachine.CWMain

/-! ## Sizes -/

theorem u_len (xs : List ℕ) : ((xs.map natWord).flatten).length = (xs.map fun x => 2 * natBitLength x + 1).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, natWord_len]

theorem sum_ge_len (xs : List ℕ) : xs.length ≤ (xs.map fun x => 2 * natBitLength x + 1).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp; omega

theorem nbl_le_sum (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    2 * natBitLength x + 1 ≤ (xs.map fun x => 2 * natBitLength x + 1).sum := by
  induction xs with
  | nil => simp at hx
  | cons y xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · have := ih h; omega

theorem len_le (xs : List ℕ) : xs.length ≤ ((xs.map natWord).flatten).length := by
  rw [u_len]; exact sum_ge_len xs

theorem nbl_le (xs : List ℕ) : ∀ x ∈ xs, natBitLength x ≤ ((xs.map natWord).flatten).length := by
  intro x hx; rw [u_len]; have := nbl_le_sum xs x hx; omega

theorem bw_len (x : ℕ) : (CWRoundA.bw x).length ≤ natBitLength x + 1 := by
  unfold CWRoundA.bw
  rw [List.length_map]
  have := CloseoutWitness.Reencode.count_bound (CWRoundA.fld x)
  unfold CloseoutWitness.TraversalCounted.count at this
  rw [CWRoundA.fld_length] at this
  exact this

theorem bots_eq (xs : List ℕ) : bots xs = (xs.map CWRoundA.bw).flatten := by
  simp [bots, CWRoundA.bacc]

theorem bots_len (xs : List ℕ) : (bots xs).length ≤ ((xs.map natWord).flatten).length := by
  rw [bots_eq, u_len]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons]
    have := bw_len x; omega

theorem bots_width (xs : List ℕ) : ∀ y ∈ bots xs, y.length ≤ ((xs.map natWord).flatten).length := by
  intro y hy
  rw [bots_eq] at hy
  obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hyl
  rw [SignedSortKey.binary_length, CWRoundA.fld_length]
  exact nbl_le xs x hx

theorem flat_le (ws : List (List Bool)) (W : ℕ) (h : ∀ w ∈ ws, w.length ≤ W) :
    (ws.flatMap frame).length ≤ ws.length * (2 * W + 1) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h w (by simp)
    have h2 := ih (fun v hv => h v (by simp [hv]))
    have : (frame w).length = 2 * w.length + 1 := by rw [frame_eq_frameP]; simp
    rw [this]; nlinarith

theorem gc_bits_le (y : List Bool) : (CWRoundB.gc y).bits.length ≤ 20 * y.length + 40 := by
  have hb := PCPPair.pair_bound [true] (CWRoundB.w3 y)
  rw [CWRoundB.pair4] at hb
  have hw : PCPPair.width [true] (CWRoundB.w3 y) = 20 * y.length + 40 := by
    simp [PCPPair.width, CWRoundB.w3_len]; ring
  rw [hw] at hb
  exact CanonicalPositiveOutput.nat_bits_length_le _ _ hb

theorem codes_eq (xs : List ℕ) : codes xs = (bots xs).map fun y => (CWRoundB.gc y).bits := by
  simp [codes, CWRoundB.gacc]

theorem codes_width (xs : List ℕ) :
    ∀ g ∈ codes xs, g.length ≤ 20 * ((xs.map natWord).flatten).length + 40 := by
  intro g hg
  rw [codes_eq] at hg
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hg
  have := gc_bits_le y
  have := bots_width xs y hy
  omega

theorem codes_len (xs : List ℕ) : (codes xs).length = (bots xs).length := by
  rw [codes_eq, List.length_map]

/-! ## The capacity -/

theorem le_cap (n a K : ℕ) (h : a ≤ K * (n + 1) ^ 24) (hK : K ≤ C0) : a ≤ cap n :=
  h.trans (Nat.mul_le_mul_right _ hK)

/-- **The capacity dominates the loops' needs.** -/
theorem caps_ok (xs : List ℕ) : Caps xs (cap ((xs.map natWord).flatten).length) := by
  set n := ((xs.map natWord).flatten).length with hn
  have hc : xs.length ≤ n := len_le xs
  have hN : (bots xs).length ≤ n := bots_len xs
  have hB : ((bots xs).flatMap frame).length ≤ n * (2 * n + 1) :=
    (flat_le _ n (bots_width xs)).trans (Nat.mul_le_mul_right _ hN)
  have hG : ((codes xs).flatMap frame).length ≤ n * (2 * (20 * n + 40) + 1) := by
    have := flat_le _ (20 * n + 40) (codes_width xs)
    rw [codes_len] at this
    exact this.trans (Nat.mul_le_mul_right _ hN)
  have hS : ((xs.map nf).flatten ++ [false]).length = 2 * n + 1 := by
    rw [← frame_fields, frame_eq_frameP]; simp [hn]
  have hQ : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have hQP : (n + 1) ^ 2 ≤ (n + 1) ^ 24 := Nat.pow_le_pow_right (by omega) (by omega)
  have hBQ : ((bots xs).flatMap frame).length ≤ 2 * (n + 1) ^ 2 := by nlinarith
  have hGQ : ((codes xs).flatMap frame).length ≤ 81 * (n + 1) ^ 2 := by nlinarith
  have hcA : xs.length * (18 * n + 16) ≤ 18 * (n + 1) ^ 2 := by
    have := Nat.mul_le_mul_right (18 * n + 16) hc; nlinarith
  have hcB : (bots xs).length * (5 * n + 8) ≤ 5 * (n + 1) ^ 2 + 3 * (n + 1) := by
    have := Nat.mul_le_mul_right (5 * n + 8) hN; nlinarith
  have e1 : (2 * n + 4) ^ 2 ≤ 16 * (n + 1) ^ 2 := by nlinarith
  have e2 : (5 * n + 9) ^ 2 ≤ 81 * (n + 1) ^ 2 := by nlinarith
  have e3 : (10 * n + 20) ^ 2 ≤ 400 * (n + 1) ^ 2 := by nlinarith
  have hn1 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hA : CWRoundA.foldCwA n xs.length ((bots xs).flatMap frame).length (bots xs).length + 1 ≤ cap n := by
    apply le_cap n _ (16 * 1000000000000000000 + 100000) _ (by unfold C0; norm_num)
    unfold CWRoundA.foldCwA
    generalize (n + 1) ^ 24 = P at *
    generalize (n + 1) ^ 2 = Q at *
    omega
  have hBB : CWRoundB.foldCwB n (bots xs).length ((codes xs).flatMap frame).length + 1 ≤ cap n := by
    apply le_cap n _ 1000000 _ (by unfold C0; norm_num)
    unfold CWRoundB.foldCwB
    generalize (n + 1) ^ 24 = P at *
    generalize (n + 1) ^ 2 = Q at *
    generalize (2 * n + 4) ^ 2 = Q1 at *
    generalize (5 * n + 9) ^ 2 = Q2 at *
    generalize (10 * n + 20) ^ 2 = Q3 at *
    omega
  refine ⟨nbl_le xs, bots_width xs, ?_, ?_, ?_, ?_, hA, ?_, hBB⟩
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

/-- The core's time coefficient. -/
def Kc : ℕ := BlockPlatform.UnaryCalc.polyCoefficient 24 C0 + 20 * C0 + 2 * 1000000000000 * 82 ^ 12 + 1000 * 82 ^ 5 + 1000

theorem mass_eq (gs : List (List Bool)) : PCPSerializerMass.mass gs = (gs.flatMap frame).length := by
  rw [← PCPTraversal.stream_mass, stream_eq]

/-- The core's fuel as a function of its ingredients. -/
def costF (n c N PB T XA XB SC NC : ℕ) : ℕ :=
  1 + 1 + ((2 * (n * 9 + 1) + 2) + 1 + ((2 * (c * (18 * n + 16) + 5) + 2) + 1 +
    (PB + 1 + ((2 * 3 + 2) + 1 + ((2 * T + 4) + 1 +
      ((1 + 1 + (c * (XA + 1 + (2 * T + 4 + 1 + 0) + 2) + c + 3 + 1 + 1)) + 1 + ((2 * T + 4) + 1 +
      ((1 + 1 + (N * (XB + 1 + (2 * T + 4 + 1 + 0) + 2) + N + 3 + 1 + 1)) + 1 +
      (SC + 1 + (2 * NC + 2))))))))))

theorem coreCost_eq (xs : List ℕ) : coreCost xs = costF ((xs.map natWord).flatten).length xs.length (bots xs).length
    (PCPSerializerCapacity.Power.budget 24 C0 ((xs.map natWord).flatten).length) (cap ((xs.map natWord).flatten).length)
    (CWRoundA.foldCwA ((xs.map natWord).flatten).length xs.length ((bots xs).flatMap frame).length (bots xs).length)
    (CWRoundB.foldCwB ((xs.map natWord).flatten).length (bots xs).length ((codes xs).flatMap frame).length)
    (serCost (codes xs)) (natCost (PCPTraversal.code (codes xs))) := rfl

/-- **The core's time is a fixed polynomial**: `coreCost xs ≤ Kc·(|u|+1)^26`. -/
theorem coreCost_le (xs : List ℕ) : coreCost xs ≤ Kc * (((xs.map natWord).flatten).length + 1) ^ 26 := by
  have hc := caps_ok xs
  set n := ((xs.map natWord).flatten).length with hn
  have hcx : xs.length ≤ n := len_le xs
  have hN : (bots xs).length ≤ n := bots_len xs
  have hG : ((codes xs).flatMap frame).length ≤ n * (2 * (20 * n + 40) + 1) := by
    have := flat_le _ (20 * n + 40) (codes_width xs)
    rw [codes_len] at this
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
  set M := PCPSerializerMass.mass (codes xs) with hM
  have hMb : M + 1 ≤ 82 * m ^ 2 := by rw [hM, mass_eq]; nlinarith
  have hM12 : (M + 1) ^ 12 ≤ 82 ^ 12 * m ^ 24 := by
    calc (M + 1) ^ 12 ≤ (82 * m ^ 2) ^ 12 := Nat.pow_le_pow_left hMb _
      _ = 82 ^ 12 * m ^ 24 := by rw [mul_pow, ← pow_mul]
  have hM5 : (M + 1) ^ 5 ≤ 82 ^ 5 * m ^ 10 := by
    calc (M + 1) ^ 5 ≤ (82 * m ^ 2) ^ 5 := Nat.pow_le_pow_left hMb _
      _ = 82 ^ 5 * m ^ 10 := by rw [mul_pow, ← pow_mul]
  have hbits : (PCPTraversal.code (codes xs)).bits.length ≤ 3 * (M + 1) ^ 5 := PCPSerializerMass.code_bits _
  have hpoly := BlockPlatform.UnaryCalc.poly_cost_polyBounded 24 C0 n
  unfold ValidatorPolynomialDomination.PolyBounded at hpoly
  have hcA : xs.length * (18 * n + 16) ≤ 18 * m ^ 2 := by
    have := Nat.mul_le_mul_right (18 * n + 16) hcx; nlinarith
  -- the loops
  have hA7 : xs.length * (CWRoundA.foldCwA n xs.length ((bots xs).flatMap frame).length (bots xs).length + 1 +
      (2 * cap n + 4 + 1 + 0) + 2) ≤ 3 * C0 * m ^ 25 + 7 * n := by
    have h1 := Nat.mul_le_mul_right (3 * cap n + 7) hcx
    have h2 : CWRoundA.foldCwA n xs.length ((bots xs).flatMap frame).length (bots xs).length + 1 +
      (2 * cap n + 4 + 1 + 0) + 2 ≤ 3 * cap n + 7 := by have := hc.a5; rw [← hn] at this; omega
    have h3 := Nat.mul_le_mul_left xs.length h2
    have h4 : n * (3 * cap n + 7) = 3 * C0 * (n * m ^ 24) + 7 * n := by rw [hT]; ring
    have h5 := Nat.mul_le_mul_left (3 * C0) hnP
    omega
  have hA9 : (bots xs).length * (CWRoundB.foldCwB n (bots xs).length ((codes xs).flatMap frame).length + 1 +
      (2 * cap n + 4 + 1 + 0) + 2) ≤ 3 * C0 * m ^ 25 + 7 * n := by
    have h1 := Nat.mul_le_mul_right (3 * cap n + 7) hN
    have h2 : CWRoundB.foldCwB n (bots xs).length ((codes xs).flatMap frame).length + 1 +
      (2 * cap n + 4 + 1 + 0) + 2 ≤ 3 * cap n + 7 := by have := hc.b4; rw [← hn] at this; omega
    have h3 := Nat.mul_le_mul_left (bots xs).length h2
    have h4 : n * (3 * cap n + 7) = 3 * C0 * (n * m ^ 24) + 7 * n := by rw [hT]; ring
    have h5 := Nat.mul_le_mul_left (3 * C0) hnP
    omega
  rw [coreCost_eq, ← hn]
  unfold costF serCost natCost PCPTraversal.budget
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
  have q5 : (PCPTraversal.code (codes xs)).bits.length ≤ 3 * 82 ^ 5 * m ^ 26 := by
    have h1 : 3 * (M + 1) ^ 5 ≤ 3 * (82 ^ 5 * m ^ 26) :=
      Nat.mul_le_mul_left _ (hM5.trans (Nat.mul_le_mul_left _ (p10.trans (p24.trans p25))))
    calc (PCPTraversal.code (codes xs)).bits.length ≤ 3 * (82 ^ 5 * m ^ 26) := hbits.trans h1
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

end NearCubicWires.WireExponent3_5.UnionMachine.CWBounds
