import Proof.Wire_3_5.Primitive.SeedFix.ThrTB1

/-! # THRTAIL T-B, part 2: the class link at the THR dimension

The THR writer's budget `128·K²·(2^m+1)^E·(2^m+1)^E` at a dimension `m ≤ k + L + K_L·L² + 8K_f·Ψ_T` (T-A's `m_le`,
`mOfT = k + L + K_L L²`) is in the preprocessing class `2^{c_ψ·Ψ}·n^{A_pre}` (P3:3108, 3112-3114) once
`2E(2 + K_L + 8K_f) ≤ c_ψ`: at `C_D ≥ 1`, `k + L² ≤ Ψ_T ≤ Ψ` (P3:3094-3107), so `m + 1 ≤ (2 + K_L + 8K_f)·Ψ + 1`.

* `pow_two_succ`, `thr_ge`; **`class_linkT`**.

Paper quantity of the main type: the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost

/-- `(2^m + 1)^e ≤ 2^{e(m+1)}`. -/
theorem pow_two_succ (m e : ℕ) : (2 ^ m + 1) ^ e ≤ 2 ^ (e * (m + 1)) := by
  have h : 2 ^ m + 1 ≤ 2 ^ (m + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := m); omega
  calc (2 ^ m + 1) ^ e ≤ (2 ^ (m + 1)) ^ e := Nat.pow_le_pow_left h e
    _ = 2 ^ (e * (m + 1)) := by rw [← pow_mul, Nat.mul_comm]

/-- `k + L² ≤ Ψ_T` at `C_D ≥ 1`. -/
theorem thr_ge (CD k L BT : ℕ) (hCD : 1 ≤ CD) : k + L ^ 2 ≤ loadThr CD k L BT := by
  unfold loadThr
  have h : k + L ^ 2 ≤ (k + L) ^ 2 * (CD * (sqrtUp (BT * L) + L ^ 2)) + k + L ^ 2 := by omega
  exact h.trans (Nat.le_mul_of_pos_left _ hCD)

/-- **The class link at the THR dimension.** -/
theorem class_linkT (EW : Envelope) (E K KL Kf CD n k L BT BS m : ℕ) (hL : 1 ≤ L) (hCD : 1 ≤ CD) (hn : 1 ≤ n)
    (hm : m ≤ k + L + KL * L ^ 2 + 8 * Kf * loadThr CD k L BT)
    (hcpsi : 2 * E * (2 + KL + 8 * Kf) ≤ EW.cpsi) :
    128 * (K * K * ((2 ^ m + 1) ^ E * (2 ^ m + 1) ^ E)) ≤
      (128 * (K * K) * 2 ^ (2 * E)) * classBound EW .preprocessing n k (loadPsi CD k L BT BS) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ p, p = loadPsi CD k L BT BS := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ p, p = loadThr CD k L BT := ⟨_, rfl⟩
  have hTΨ : T ≤ Ψ := by rw [hΨ, hT]; exact le_max_left _ _
  have hkT : k + L ^ 2 ≤ T := by rw [hT]; exact thr_ge CD k L BT hCD
  rw [← hT] at hm
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hm1 : m + 1 ≤ (2 + KL + 8 * Kf) * Ψ + 1 := by
    have a1 : KL * L ^ 2 ≤ KL * Ψ := Nat.mul_le_mul_left _ (by omega)
    have a2 : 8 * Kf * T ≤ 8 * Kf * Ψ := Nat.mul_le_mul_left _ hTΨ
    have e : (2 + KL + 8 * Kf) * Ψ = 2 * Ψ + KL * Ψ + 8 * Kf * Ψ := by ring
    omega
  have h1 : (2 ^ m + 1) ^ E * (2 ^ m + 1) ^ E ≤ 2 ^ (2 * E * (m + 1)) := by
    rw [← pow_add]
    have := pow_two_succ m (E + E)
    rw [show (E + E) * (m + 1) = 2 * E * (m + 1) by ring] at this
    exact this
  have h2 : 2 ^ (2 * E * (m + 1)) ≤ 2 ^ (2 * E) * 2 ^ (EW.cpsi * Ψ) := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    have b1 : 2 * E * (m + 1) ≤ 2 * E * ((2 + KL + 8 * Kf) * Ψ + 1) := Nat.mul_le_mul_left _ hm1
    have b2 : 2 * E * ((2 + KL + 8 * Kf) * Ψ) ≤ EW.cpsi * Ψ := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hcpsi
    have e : 2 * E * ((2 + KL + 8 * Kf) * Ψ + 1) = 2 * E * ((2 + KL + 8 * Kf) * Ψ) + 2 * E := by ring
    omega
  have h3 : 2 ^ (EW.cpsi * Ψ) ≤ classBound EW .preprocessing n k Ψ := by
    show 2 ^ (EW.cpsi * Ψ) ≤ 2 ^ (EW.cpsi * Ψ) * n ^ EW.Apre
    exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hn)
  rw [← hΨ]
  calc 128 * (K * K * ((2 ^ m + 1) ^ E * (2 ^ m + 1) ^ E))
      ≤ 128 * (K * K * (2 ^ (2 * E) * classBound EW .preprocessing n k Ψ)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (h1.trans (h2.trans (Nat.mul_le_mul_left _ h3))))
    _ = _ := by ring

end NearCubicWires.WireExponent3_5.PrimT.ThrTB
