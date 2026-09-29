import Proof.Wire_3_5.Primitive.Writers.HashSizes

/-! # (HASH (d4)), part 2: the class link at the HASH dimension

The HASH writer's budget is `K·(2^m + 1)^E` at the dimension `m = k + L + K_L·L² + K_H·L³` (`NumsXH.mOfH`, `k` the
star width `kOf n`, `L = ⌈log₂(n+2)⌉`), with `E` fixed with the floors and `K`, `K_L`, `K_H` after `F`. The
preprocessing class is `2^{c_ψ·Ψ}·n^{A_pre}` (P3:3108, 3112-3114) with `Ψ ≥ Ψ_aux = C_D[k + L² + (k+L³)L²(k+L)]`
(P3:3101-3102). At `C_D ≥ 1`, `Ψ ≥ k + L⁶`, so `E(m+1) ≤ E·Ψ + c₀² + E` with `c₀ = E(1+K_L+K_H)`
(`c₀L³ ≤ L⁶ + c₀²`): the budget is at most `K·2^{c₀²+E}·2^{E·Ψ}`.

* `loadPsi_ge` (`k + L⁶ ≤ Ψ`), `exp_link`, `pow_succ_le` (`(2^m+1)^E ≤ 2^{E(m+1)}`);
* **`class_link`**: `K·(2^m+1)^E ≤ (K·2^{c₀²+E})·classBound E_W .preprocessing n k Ψ` whenever `E ≤ c_ψ(E_W)`.

Paper quantity of the main type: the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashSizes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost

/-- **`Ψ ≥ k + L⁶`** at `C_D ≥ 1`. -/
theorem loadPsi_ge (CD k L BT BS : ℕ) (hCD : 1 ≤ CD) : k + L ^ 6 ≤ loadPsi CD k L BT BS := by
  have h1 : loadAux CD k L ≤ loadPsi CD k L BT BS := le_trans (le_max_right _ _) (le_max_right _ _)
  refine le_trans ?_ h1
  unfold loadAux
  have h2 : L ^ 6 ≤ (k + L ^ 3) * L ^ 2 * (k + L) := by
    have a1 : L ^ 3 ≤ k + L ^ 3 := Nat.le_add_left _ _
    have a2 : L ≤ k + L := Nat.le_add_left _ _
    calc L ^ 6 = L ^ 3 * L ^ 2 * L := by ring
      _ ≤ (k + L ^ 3) * L ^ 2 * (k + L) := Nat.mul_le_mul (Nat.mul_le_mul_right _ a1) a2
  have h3 : k + L ^ 6 ≤ k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L) := by omega
  calc k + L ^ 6 ≤ k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L) := h3
    _ = 1 * (k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L)) := (one_mul _).symm
    _ ≤ CD * (k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L)) := Nat.mul_le_mul_right _ hCD

/-- **The exponent link**: `E(k + L + K_L L² + K_H L³ + 1) ≤ E·Ψ + (E(1+K_L+K_H))² + E`. -/
theorem exp_link (E KL KH k L psi : ℕ) (hE : 1 ≤ E) (hL : 1 ≤ L) (hpsi : k + L ^ 6 ≤ psi) :
    E * (k + L + KL * L ^ 2 + KH * L ^ 3 + 1) ≤ E * psi + (E * (1 + KL + KH)) ^ 2 + E := by
  obtain ⟨c, hc⟩ : ∃ c, c = E * (1 + KL + KH) := ⟨_, rfl⟩
  have hL2 : L ≤ L ^ 3 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 3 := Nat.pow_le_pow_right hL (by norm_num)
  have hL23 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right hL (by norm_num)
  have h1 : E * (L + KL * L ^ 2 + KH * L ^ 3) ≤ c * L ^ 3 := by
    rw [hc]
    have : L + KL * L ^ 2 + KH * L ^ 3 ≤ (1 + KL + KH) * L ^ 3 := by
      have b1 : KL * L ^ 2 ≤ KL * L ^ 3 := Nat.mul_le_mul_left _ hL23
      have e : (1 + KL + KH) * L ^ 3 = L ^ 3 + KL * L ^ 3 + KH * L ^ 3 := by ring
      omega
    calc E * (L + KL * L ^ 2 + KH * L ^ 3) ≤ E * ((1 + KL + KH) * L ^ 3) := Nat.mul_le_mul_left _ this
      _ = E * (1 + KL + KH) * L ^ 3 := by ring
  have h2 : c * L ^ 3 ≤ L ^ 6 + c ^ 2 := by
    have e : L ^ 6 = L ^ 3 * L ^ 3 := by ring
    rw [e, sq]
    nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le c]
  have e : E * (k + L + KL * L ^ 2 + KH * L ^ 3 + 1) = E * k + E * (L + KL * L ^ 2 + KH * L ^ 3) + E := by ring
  have hEk : E * k + L ^ 6 ≤ E * psi := by
    have a1 : E * (k + L ^ 6) ≤ E * psi := Nat.mul_le_mul_left _ hpsi
    have a2 : L ^ 6 ≤ E * L ^ 6 := Nat.le_mul_of_pos_left _ hE
    have e2 : E * (k + L ^ 6) = E * k + E * L ^ 6 := by ring
    omega
  rw [e, ← hc]
  omega

/-- `(2^m + 1)^E ≤ 2^{E(m+1)}`. -/
theorem pow_succ_le (m E : ℕ) : (2 ^ m + 1) ^ E ≤ 2 ^ (E * (m + 1)) := by
  have h : 2 ^ m + 1 ≤ 2 ^ (m + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := m); omega
  calc (2 ^ m + 1) ^ E ≤ (2 ^ (m + 1)) ^ E := Nat.pow_le_pow_left h E
    _ = 2 ^ (E * (m + 1)) := by rw [← pow_mul]; ring_nf

/-- **The class link**: at `m = k + L + K_L L² + K_H L³`, `C_D ≥ 1`, `E ≤ c_ψ`, the budget `K·(2^m+1)^E` is within
`(K·2^{(E(1+K_L+K_H))² + E})·classBound E_W .preprocessing n k Ψ`. -/
theorem class_link (EW : Envelope) (E K KL KH CD n k L BT BS : ℕ) (hE : 1 ≤ E) (hL : 1 ≤ L) (hCD : 1 ≤ CD)
    (hcpsi : E ≤ EW.cpsi) (hn : 1 ≤ n) :
    K * (2 ^ (k + L + KL * L ^ 2 + KH * L ^ 3) + 1) ^ E ≤
      (K * 2 ^ ((E * (1 + KL + KH)) ^ 2 + E)) * classBound EW .preprocessing n k (loadPsi CD k L BT BS) := by
  have hpsi := loadPsi_ge CD k L BT BS hCD
  have h1 := pow_succ_le (k + L + KL * L ^ 2 + KH * L ^ 3) E
  have h2 := exp_link E KL KH k L (loadPsi CD k L BT BS) hE hL hpsi
  have h3 : 2 ^ (E * (k + L + KL * L ^ 2 + KH * L ^ 3 + 1)) ≤
      2 ^ ((E * (1 + KL + KH)) ^ 2 + E) * 2 ^ (E * loadPsi CD k L BT BS) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (E * loadPsi CD k L BT BS) ≤ classBound EW .preprocessing n k (loadPsi CD k L BT BS) := by
    show 2 ^ (E * loadPsi CD k L BT BS) ≤ 2 ^ (EW.cpsi * loadPsi CD k L BT BS) * n ^ EW.Apre
    have a1 : 2 ^ (E * loadPsi CD k L BT BS) ≤ 2 ^ (EW.cpsi * loadPsi CD k L BT BS) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hcpsi)
    have a2 : 1 ≤ n ^ EW.Apre := Nat.one_le_pow _ _ hn
    calc 2 ^ (E * loadPsi CD k L BT BS) ≤ 2 ^ (EW.cpsi * loadPsi CD k L BT BS) * 1 := by rw [mul_one]; exact a1
      _ ≤ _ := Nat.mul_le_mul_left _ a2
  calc K * (2 ^ (k + L + KL * L ^ 2 + KH * L ^ 3) + 1) ^ E
      ≤ K * (2 ^ ((E * (1 + KL + KH)) ^ 2 + E) * 2 ^ (E * loadPsi CD k L BT BS)) :=
        Nat.mul_le_mul_left _ (le_trans h1 h3)
    _ ≤ K * (2 ^ ((E * (1 + KL + KH)) ^ 2 + E) * classBound EW .preprocessing n k (loadPsi CD k L BT BS)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
    _ = _ := by ring

end NearCubicWires.WireExponent3_5.PrimAsm.HashSizes
