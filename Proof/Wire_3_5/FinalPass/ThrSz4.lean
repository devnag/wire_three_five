import Proof.Wire_3_5.FinalPass.ThrSz3

/-! # The THR call's sizes, part 4: coefficient-times-power bounds

`x ≤ K·N^d` bounds combine with the exponent kept apart from the coefficient (StageU's order: the exponent is chosen
before the gate): `kn_add`, `kn_mul`, `kn_mono`, `kn_one`, `kn_const`. With them: **`table_kn`** (the tuple's gate
table `≤ 2253·N^79` at `N = n+1`, descriptions `≤ N^26`), **`level_kn`** (stage 4's table `≤ K_ℓ·N^{3d}` from
`M, J, t, B_* ≤ K·N^d`). Paper quantity: none beyond arithmetic (the call's words are polynomial, P3:3176-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrSz
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.SupplierPipeline

section KN
variable {N : ℕ}

theorem kn_mono (hN : 1 ≤ N) {x K a b : ℕ} (h : x ≤ K * N ^ a) (hab : a ≤ b) : x ≤ K * N ^ b :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN hab))

theorem kn_mul {x y K1 K2 a b : ℕ} (h1 : x ≤ K1 * N ^ a) (h2 : y ≤ K2 * N ^ b) : x * y ≤ (K1 * K2) * N ^ (a + b) := by
  calc x * y ≤ (K1 * N ^ a) * (K2 * N ^ b) := Nat.mul_le_mul h1 h2
    _ = (K1 * K2) * N ^ (a + b) := by rw [pow_add]; ring

theorem kn_one (x d : ℕ) (h : x ≤ N ^ d) : x ≤ 1 * N ^ d := by rw [Nat.one_mul]; exact h

end KN

/-- **The gate table's length** at descriptions `≤ (n+1)^26`. -/
theorem table_kn {n a' : ℕ} (ha : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    (FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)).length ≤
      2253 * (n + 1) ^ 79 := by
  have hN : 1 ≤ n + 1 := by omega
  have hL1 : 1 ≤ (n + 1) ^ 26 := Nat.one_le_pow _ _ hN
  have hn26 : n ≤ (n + 1) ^ 26 := le_trans (by omega) (Nat.le_self_pow (by norm_num) (n + 1))
  have hG : (PrimT.ThrTab.tupleG Cs).length ≤ 4 * (n + 1) ^ 26 := by
    unfold PrimT.ThrTab.tupleG
    rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    calc ∑ i, (List.length ∘ fun j => (SupplierEstimator.thresholdCircuitOccurrences (Cs j)).map (·.gate)) i
        ≤ ∑ _i : Fin a', (n + 1) ^ 26 := Finset.sum_le_sum (fun i _ => by
          show ((SupplierEstimator.thresholdCircuitOccurrences (Cs i)).map (·.gate)).length ≤ _
          rw [List.length_map]; exact (occ_len _).trans (hd i))
      _ = a' * (n + 1) ^ 26 := by simp
      _ ≤ 4 * (n + 1) ^ 26 := Nat.mul_le_mul_right _ ha
  have hh0 := tabH_le ha Cs ((n + 1) ^ 26) hd
  have h35 : 8 * n + 8 * (n + 1) ^ 26 + 19 ≤ 35 * (n + 1) ^ 26 := by omega
  have hh : PrimT.tabH (PrimT.ThrTab.tupleG Cs) ≤ 140 * (n + 1) ^ 52 := by
    refine hh0.trans ?_
    calc 4 * (n + 1) ^ 26 * (8 * n + 8 * (n + 1) ^ 26 + 19) ≤ 4 * (n + 1) ^ 26 * (35 * (n + 1) ^ 26) :=
          Nat.mul_le_mul_left _ h35
      _ = 140 * (n + 1) ^ 52 := by rw [show 52 = 26 + 26 from rfl, pow_add]; ring
  rw [ThrPt.gatesW_len]
  set h := PrimT.tabH (PrimT.ThrTab.tupleG Cs)
  set g := (PrimT.ThrTab.tupleG Cs).length
  have h52 : 1 ≤ (n + 1) ^ 52 := Nat.one_le_pow _ _ hN
  have hA : 2 * (2 * h + 1) ≤ 562 * (n + 1) ^ 52 := by omega
  have hB : (n + 1) * (2 * (2 * h + 1)) ≤ 562 * (n + 1) ^ 53 := by
    calc (n + 1) * (2 * (2 * h + 1)) ≤ (n + 1) * (562 * (n + 1) ^ 52) := Nat.mul_le_mul_left _ hA
      _ = 562 * (n + 1) ^ 53 := by rw [show 53 = 52 + 1 from rfl, pow_succ]; ring
  have h53 : 1 ≤ (n + 1) ^ 53 := Nat.one_le_pow _ _ hN
  have hC : 1 + (n + 1) * (2 * (2 * h + 1)) ≤ 563 * (n + 1) ^ 53 := by omega
  have hD : g * (1 + (n + 1) * (2 * (2 * h + 1))) ≤ 2252 * (n + 1) ^ 79 := by
    calc g * (1 + (n + 1) * (2 * (2 * h + 1))) ≤ (4 * (n + 1) ^ 26) * (563 * (n + 1) ^ 53) := Nat.mul_le_mul hG hC
      _ = 2252 * (n + 1) ^ 79 := by rw [show 79 = 26 + 53 from rfl, pow_add]; ring
  have h79 : 1 ≤ (n + 1) ^ 79 := Nat.one_le_pow _ _ hN
  have e : 1 + (n + 1) * (2 * (2 * h + 1)) = 1 + (n + 1) * (2 * (2 * h + 1)) := rfl
  omega

/-- **Stage 4's table** from `M, J, t, B_* ≤ K·N^d` (rows of length `L ≤ K·N^d`). -/
theorem level_kn (MP : Filters.MajorantParams) (L : ℕ) (row : ℕ → List Bool) (hrow : ∀ j, (row j).length = L)
    {N K d : ℕ} (hN : 1 ≤ N) (hM : MP.M ≤ K * N ^ d) (hJ : MP.J ≤ K * N ^ d) (ht : MP.t ≤ K * N ^ d)
    (hB : MP.Bstar ≤ K * N ^ d) (hL : L ≤ K * N ^ d) :
    (ListEval.levelWord MP.M MP.J MP.W row).length ≤
      (K + 2 + (K + 1) * (5 * (16 * K + 20 * (K * K + 2)) + 5 + K)) * N ^ (3 * d) := by
  have hd1 : 1 ≤ N ^ d := Nat.one_le_pow _ _ hN
  have h2d : N ^ d ≤ N ^ (2 * d) := Nat.pow_le_pow_right hN (by omega)
  have h3d : N ^ (2 * d) ≤ N ^ (3 * d) := Nat.pow_le_pow_right hN (by omega)
  have htB : MP.t * MP.Bstar ≤ (K * K) * N ^ (2 * d) := by
    have := kn_mul ht hB; rwa [show d + d = 2 * d by ring] at this
  have hWm : 16 * MP.t + 20 * (MP.t * MP.Bstar + 2) ≤ (16 * K + 20 * (K * K + 2)) * N ^ (2 * d) := by
    have e1 : 16 * MP.t ≤ 16 * K * N ^ (2 * d) := by
      have := Nat.mul_le_mul_left 16 (kn_mono hN ht (show d ≤ 2 * d by omega)); rwa [← Nat.mul_assoc] at this
    have e2 : 1 ≤ N ^ (2 * d) := Nat.one_le_pow _ _ hN
    have e : (16 * K + 20 * (K * K + 2)) * N ^ (2 * d) =
        16 * K * N ^ (2 * d) + 20 * ((K * K) * N ^ (2 * d)) + 40 * N ^ (2 * d) := by ring
    rw [e]
    omega
  have hlw := levelWord_le MP.M MP.J MP.W row (16 * MP.t + 20 * (MP.t * MP.Bstar + 2)) L (majW_le MP)
    (fun j => (hrow j).le)
  refine hlw.trans ?_
  set X := 16 * K + 20 * (K * K + 2)
  have hW5 : 5 * (16 * MP.t + 20 * (MP.t * MP.Bstar + 2)) + 5 + L ≤ (5 * X + 5 + K) * N ^ (2 * d) := by
    have e2 : 1 ≤ N ^ (2 * d) := Nat.one_le_pow _ _ hN
    have e3 : L ≤ K * N ^ (2 * d) := kn_mono hN hL (by omega)
    have e : (5 * X + 5 + K) * N ^ (2 * d) = 5 * (X * N ^ (2 * d)) + 5 * N ^ (2 * d) + K * N ^ (2 * d) := by ring
    rw [e]
    omega
  have hJ1 : MP.J + 1 ≤ (K + 1) * N ^ d := by rw [Nat.add_mul, Nat.one_mul]; omega
  have hprod : (MP.J + 1) * (5 * (16 * MP.t + 20 * (MP.t * MP.Bstar + 2)) + 5 + L) ≤
      ((K + 1) * (5 * X + 5 + K)) * N ^ (3 * d) := by
    have := kn_mul hJ1 hW5; rwa [show d + 2 * d = 3 * d by ring] at this
  have hM3 : MP.M ≤ K * N ^ (3 * d) := kn_mono hN hM (by omega)
  have h3 : 1 ≤ N ^ (3 * d) := Nat.one_le_pow _ _ hN
  have e : (K + 2 + (K + 1) * (5 * X + 5 + K)) * N ^ (3 * d) =
      K * N ^ (3 * d) + 2 * N ^ (3 * d) + ((K + 1) * (5 * X + 5 + K)) * N ^ (3 * d) := by ring
  rw [e]
  omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrSz
