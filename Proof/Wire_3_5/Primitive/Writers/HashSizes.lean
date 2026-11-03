import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5

/-! # (HASH (d4)), part 1: the aux filter's error exponent is `O(L²)`

The aux filter's error exponent `e = listE A B_* M K` (`Primitive.thrCallE`, P3:2210-2211, `ε_aux = 2^{−D_aux L²}`)
is a `⌈log₂⌉` of a product with the power `M^{2t}`, `t = O(log)`. From `A, B_*, M, K ≤ 2^a`:

* `listJ_le` (`J ≤ 3a + 4`), `listT_le` (`t ≤ 5a + 9`), **`listE_le`** (`e ≤ 10a² + 23a + 10`);
* `hashNums_getD_mem`, **`hashNums_ee_le`**: every entry of `ThrData.hashNums` at most `2^a` bounds entry 13
  (`e`, `ThrData.hashNums`'s `ee`) by `10a² + 23a + 10`;
* `pow_le_two_pow`: `K·(n+1)^D ≤ 2^{⌈log₂ K⌉ + D·⌈log₂(n+2)⌉}` (so `a = O(L)` at a polynomial bound).

Paper quantity of the main type: the aux filter's error exponent `e = Θ(D·L²)` (P3:2210-2211). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashSizes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline

theorem two_pow_mul3 (a : ℕ) : (2 : ℕ) ^ a * 2 ^ a * 2 ^ a = 2 ^ (3 * a) := by
  rw [← pow_add, ← pow_add]; ring_nf

/-- `J ≤ 3a + 4`. -/
theorem listJ_le {A Bs K a : ℕ} (hA : A ≤ 2 ^ a) (hB : Bs ≤ 2 ^ a) (hK : K ≤ 2 ^ a) :
    Primitive.listJ A Bs K ≤ 3 * a + 4 := by
  unfold Primitive.listJ
  apply Nat.clog_le_of_le_pow
  have h1 : K * A * Bs ≤ 2 ^ a * 2 ^ a * 2 ^ a := Nat.mul_le_mul (Nat.mul_le_mul hK hA) hB
  rw [two_pow_mul3] at h1
  have h2 : (2 : ℕ) ^ (3 * a + 4) = 16 * 2 ^ (3 * a) := by rw [pow_add]; ring
  have h3 : 1 ≤ (2 : ℕ) ^ (3 * a) := Nat.one_le_two_pow
  have e : 8 * K * A * Bs = 8 * (K * A * Bs) := by ring
  rw [h2, e]
  generalize K * A * Bs = u at h1 ⊢
  generalize (2 : ℕ) ^ (3 * a) = v at h1 h3 ⊢
  omega

/-- `J < 2^{3a+4}`. -/
theorem listJ_le_pow {A Bs K a : ℕ} (hA : A ≤ 2 ^ a) (hB : Bs ≤ 2 ^ a) (hK : K ≤ 2 ^ a) :
    Primitive.listJ A Bs K ≤ 2 ^ (3 * a + 4) :=
  le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by norm_num) (listJ_le hA hB hK))

/-- `t ≤ 5a + 9`. -/
theorem listT_le {A Bs K a : ℕ} (hA : A ≤ 2 ^ a) (hB : Bs ≤ 2 ^ a) (hK : K ≤ 2 ^ a) :
    Primitive.listT A Bs K ≤ 5 * a + 9 := by
  unfold Primitive.listT
  have hJ := listJ_le_pow hA hB hK
  have hc : Nat.clog 2 (8 * K * A * Primitive.listJ A Bs K + 1) ≤ 5 * a + 8 := by
    apply Nat.clog_le_of_le_pow
    have h1 : K * A * Primitive.listJ A Bs K ≤ 2 ^ a * 2 ^ a * 2 ^ (3 * a + 4) :=
      Nat.mul_le_mul (Nat.mul_le_mul hK hA) hJ
    have e1 : (2 : ℕ) ^ a * 2 ^ a * 2 ^ (3 * a + 4) = 2 ^ (5 * a + 4) := by rw [← pow_add, ← pow_add]; ring_nf
    rw [e1] at h1
    have h2 : (2 : ℕ) ^ (5 * a + 8) = 16 * 2 ^ (5 * a + 4) := by
      rw [show 5 * a + 8 = (5 * a + 4) + 4 by ring, pow_add]; ring
    have h3 : 1 ≤ (2 : ℕ) ^ (5 * a + 4) := Nat.one_le_two_pow
    have e : 8 * K * A * Primitive.listJ A Bs K = 8 * (K * A * Primitive.listJ A Bs K) := by ring
    rw [h2, e]
    generalize K * A * Primitive.listJ A Bs K = u at h1 ⊢
    generalize (2 : ℕ) ^ (5 * a + 4) = v at h1 h3 ⊢
    omega
  omega

/-- **The aux error exponent**: `e = listE A B_* M K ≤ 10a² + 23a + 10` when `A, B_*, M, K ≤ 2^a`. -/
theorem listE_le {A Bs M K a : ℕ} (hA : A ≤ 2 ^ a) (hB : Bs ≤ 2 ^ a) (hM : M ≤ 2 ^ a) (hK : K ≤ 2 ^ a) :
    Primitive.listE A Bs M K ≤ 10 * a * a + 23 * a + 10 := by
  unfold Primitive.listE
  have hJ := listJ_le_pow hA hB hK
  have ht := listT_le hA hB hK
  obtain ⟨t, rfl⟩ : ∃ t, t = Primitive.listT A Bs K := ⟨_, rfl⟩
  obtain ⟨J, rfl⟩ : ∃ J, J = Primitive.listJ A Bs K := ⟨_, rfl⟩
  have hc : Nat.clog 2 (8 * K * A * (M + Primitive.listJ A Bs K * M ^ (2 * Primitive.listT A Bs K)) + 1) ≤
      5 * a + 9 + 2 * Primitive.listT A Bs K * a := by
    apply Nat.clog_le_of_le_pow
    generalize Primitive.listT A Bs K = t at ht ⊢
    generalize Primitive.listJ A Bs K = J at hJ ⊢
    have hMp : M ^ (2 * t) ≤ 2 ^ (2 * t * a) :=
      calc M ^ (2 * t) ≤ (2 ^ a) ^ (2 * t) := Nat.pow_le_pow_left hM _
        _ = 2 ^ (2 * t * a) := by rw [← pow_mul]; ring_nf
    have hJM : J * M ^ (2 * t) ≤ 2 ^ (3 * a + 4 + 2 * t * a) := by
      rw [pow_add]; exact Nat.mul_le_mul hJ hMp
    have hM2 : M ≤ 2 ^ (3 * a + 4 + 2 * t * a) :=
      le_trans hM (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hS : M + J * M ^ (2 * t) ≤ 2 ^ (3 * a + 5 + 2 * t * a) := by
      rw [show 3 * a + 5 + 2 * t * a = (3 * a + 4 + 2 * t * a) + 1 by ring, pow_succ]; omega
    have hKA : K * A * (M + J * M ^ (2 * t)) ≤ 2 ^ a * 2 ^ a * 2 ^ (3 * a + 5 + 2 * t * a) :=
      Nat.mul_le_mul (Nat.mul_le_mul hK hA) hS
    have e1 : (2 : ℕ) ^ a * 2 ^ a * 2 ^ (3 * a + 5 + 2 * t * a) = 2 ^ (5 * a + 5 + 2 * t * a) := by
      rw [← pow_add, ← pow_add]; ring_nf
    rw [e1] at hKA
    have h2 : (2 : ℕ) ^ (5 * a + 9 + 2 * t * a) = 16 * 2 ^ (5 * a + 5 + 2 * t * a) := by
      rw [show 5 * a + 9 + 2 * t * a = (5 * a + 5 + 2 * t * a) + 4 by ring, pow_add]; ring
    have h3 : 1 ≤ (2 : ℕ) ^ (5 * a + 5 + 2 * t * a) := Nat.one_le_two_pow
    have e : 8 * K * A * (M + J * M ^ (2 * t)) = 8 * (K * A * (M + J * M ^ (2 * t))) := by ring
    rw [h2, e]
    generalize K * A * (M + J * M ^ (2 * t)) = u at hKA ⊢
    generalize (2 : ℕ) ^ (5 * a + 5 + 2 * t * a) = v at hKA h3 ⊢
    omega
  have hta : 2 * Primitive.listT A Bs K * a ≤ 2 * (5 * a + 9) * a :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ht)
  have e2 : 2 * (5 * a + 9) * a = 10 * a * a + 18 * a := by ring
  omega

/-! ## Entry 13 of the numbers -/

theorem hashNums_getD_mem (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (cs : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp capT k : ℕ)
    (hk : k < 16) : (ThrData.hashNums P Cs cs alg Dexp capT).getD k 0 ∈ ThrData.hashNums P Cs cs alg Dexp capT := by
  have hl := ThrData.hashNums_length P Cs cs alg Dexp capT
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

/-- **Entry 13 (`e`) from a bound on every entry.** -/
theorem hashNums_ee_le (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (cs : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp capT a : ℕ)
    (h : ∀ v ∈ ThrData.hashNums P Cs cs alg Dexp capT, v ≤ 2 ^ a) :
    (ThrData.hashNums P Cs cs alg Dexp capT).getD 13 0 ≤ 10 * a * a + 23 * a + 10 := by
  have g : ∀ k, k < 16 → (ThrData.hashNums P Cs cs alg Dexp capT).getD k 0 ≤ 2 ^ a :=
    fun k hk => h _ (hashNums_getD_mem P Cs cs alg Dexp capT k hk)
  have h3 := g 3 (by norm_num)
  have h8 := g 8 (by norm_num)
  have h9 := g 9 (by norm_num)
  have h10 := g 10 (by norm_num)
  exact listE_le h9 h10 h8 h3

/-- `K·(n+1)^D ≤ 2^{⌈log₂ K⌉ + D·⌈log₂(n+2)⌉}`. -/
theorem pow_le_two_pow (K D n : ℕ) : K * (n + 1) ^ D ≤ 2 ^ (Nat.clog 2 K + D * Nat.clog 2 (n + 2)) := by
  have hK : K ≤ 2 ^ Nat.clog 2 K := Nat.le_pow_clog (by norm_num) K
  have hn : n + 1 ≤ 2 ^ Nat.clog 2 (n + 2) :=
    le_trans (by omega) (Nat.le_pow_clog (by norm_num) (n + 2))
  have hp : (n + 1) ^ D ≤ 2 ^ (D * Nat.clog 2 (n + 2)) := by
    rw [show D * Nat.clog 2 (n + 2) = Nat.clog 2 (n + 2) * D by ring, pow_mul]
    exact Nat.pow_le_pow_left hn D
  rw [pow_add]
  exact Nat.mul_le_mul hK hp

end NearCubicWires.WireExponent3_5.PrimAsm.HashSizes
