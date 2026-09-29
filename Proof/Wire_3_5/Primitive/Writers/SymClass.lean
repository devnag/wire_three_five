import Proof.Wire_3_5.Primitive.Writers.SymSizes
import Proof.Wire_3_5.Primitive.Writers.HashClass

/-! # SYM leaf, part 2: the class link at the SYM dimension

The SYM writer's budget is `K·(2^{m_S} + 1)^E`, `m_S = k + L + K_F·L² + T` (`NumsXS.mS`), with the POP term
`T = (((bitlen(8192·B_S) + 9)·(4⌈√(2^{25}B_S)⌉ + 257))·3 + 1)·(L·D₂ + K₀)` (`NumsXS.tS`). The load has
`Ψ ≥ Ψ_S ≥ (k+L)²·(⌊√B_S⌋ + 1)` and `Ψ ≥ Ψ_aux ≥ k + L⁶` at `C_D ≥ 1` (P3:3094-3102). With `σ = ⌊√B_S⌋ + 1`,
`⌈√(2^{25}B_S)⌉ ≤ 8192·σ` and `bitlen(8192·B_S) + 9 ≤ λ + Z·L` (`B_S ≤ capK·2^{ZL}`, `λ = ⌈log₂ capK⌉ + 23`):
`T ≤ a·Z·D₂·L²σ + c₂·Lσ + c₃·σ + L·D₂ + K₀` (`a = 3·2^{16}`), the first at most `a·Z·D₂·Ψ`, the others at most `Ψ`
plus a constant (below `L = c` the cap is bounded). So `E(m_S + 1) ≤ E·c_S·Ψ + c_F` with the fe-level
`c_S = a·Z·D₂ + D₂ + 3`, the constant `c_F` after `F`.

* `sqrt25_le`, `bitlen_le`, `tS_le`, `small_or` (the split), **`exp_linkS`**, **`class_linkS`**.

Paper quantity of the main type: the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114) of the SYM writer's
tape. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost

/-- `⌈√(2^{25}·B)⌉ ≤ 8192·(⌊√B⌋ + 1)`. -/
theorem sqrt25_le (B : ℕ) : CanonicalFourfoldRowProgram.natCeilSqrt (B * 33554432) ≤ 8192 * (Nat.sqrt B + 1) := by
  apply natCeilSqrt_le_of
  have h : B < (Nat.sqrt B + 1) * (Nat.sqrt B + 1) := Nat.lt_succ_sqrt B
  have e : 8192 * (Nat.sqrt B + 1) * (8192 * (Nat.sqrt B + 1)) = 67108864 * ((Nat.sqrt B + 1) * (Nat.sqrt B + 1)) := by ring
  rw [e]
  omega

/-- `bitlen(8192·B) + 9 ≤ ⌈log₂ K⌉ + Z·L + 23` whenever `B ≤ K·2^{ZL}`. -/
theorem bitlen_le (B K Z L : ℕ) (hB : B ≤ K * 2 ^ (Z * L)) :
    natBitLength (B * 8192) + 9 ≤ Nat.clog 2 K + Z * L + 23 := by
  have hK : K ≤ 2 ^ Nat.clog 2 K := Nat.le_pow_clog (by norm_num) K
  have h1 : B * 8192 ≤ 2 ^ (Nat.clog 2 K + Z * L + 13) := by
    have : B * 8192 ≤ 2 ^ Nat.clog 2 K * 2 ^ (Z * L) * 8192 :=
      Nat.mul_le_mul_right _ (le_trans hB (Nat.mul_le_mul_right _ hK))
    rw [pow_add, pow_add]; norm_num at this ⊢; linarith
  have h2 : Nat.log 2 (B * 8192) ≤ Nat.clog 2 K + Z * L + 13 := by
    calc Nat.log 2 (B * 8192) ≤ Nat.log 2 (2 ^ (Nat.clog 2 K + Z * L + 13)) := Nat.log_mono_right h1
      _ = Nat.clog 2 K + Z * L + 13 := Nat.log_pow (by norm_num) _
  unfold natBitLength; omega

/-- The SYM dimension's POP term, as `NumsXS.tS` writes it. -/
def tSOf (capS D2 K0 L : ℕ) : ℕ :=
  (((natBitLength (capS * 8192) + 9) * (2 * (2 * CanonicalFourfoldRowProgram.natCeilSqrt (capS * 33554432)) + 257)) * 3 + 1) *
    (L * D2 + K0)

/-- **The POP term's shape**: `T ≤ (a·(λ + ZL)·σ + 1)·(L·D₂ + K₀)`. -/
theorem tS_le (capS capK Z L D2 K0 : ℕ) (hB : capS ≤ capK * 2 ^ (Z * L)) :
    tSOf capS D2 K0 L ≤ (196608 * (Nat.clog 2 capK + 23 + Z * L) * (Nat.sqrt capS + 1) + 1) * (L * D2 + K0) := by
  unfold tSOf
  apply Nat.mul_le_mul_right
  have h1 := bitlen_le capS capK Z L hB
  have h2 := sqrt25_le capS
  have h3 : 2 * (2 * CanonicalFourfoldRowProgram.natCeilSqrt (capS * 33554432)) + 257 ≤ 65536 * (Nat.sqrt capS + 1) := by omega
  have h4 := Nat.mul_le_mul h1 h3
  have e : 196608 * (Nat.clog 2 capK + 23 + Z * L) * (Nat.sqrt capS + 1) =
      (Nat.clog 2 capK + Z * L + 23) * (65536 * (Nat.sqrt capS + 1)) * 3 := by ring
  rw [e]
  have := Nat.mul_le_mul_right 3 h4
  omega

/-- The SYM class constant `c_F` (after `F`). -/
def cFOf (E KF Z D2 K0 capK : ℕ) : ℕ :=
  (E * (1 + KF + 0)) ^ 2 + E +
    E * ((196608 * (Z * K0 + (Nat.clog 2 capK + 23) * D2)) * ((196608 * (Z * K0 + (Nat.clog 2 capK + 23) * D2)) *
        (capK * 2 ^ (Z * (196608 * (Z * K0 + (Nat.clog 2 capK + 23) * D2))) + 1)) +
      196608 * (Nat.clog 2 capK + 23) * K0 * (capK * 2 ^ (Z * (196608 * (Nat.clog 2 capK + 23) * K0)) + 1) + K0)

/-- The SYM class exponent `c_S` (fe-level). -/
def cSOf (Z D2 : ℕ) : ℕ := 196608 * Z * D2 + D2 + 3

theorem sqrt_le_self1 (x : ℕ) : Nat.sqrt x + 1 ≤ x + 1 := by have := Nat.sqrt_le_self x; omega

/-- **The exponent link at `m_S`**. -/
theorem exp_linkS (E KF Z D2 K0 capS capK k L ψ : ℕ) (hE : 1 ≤ E) (hL : 1 ≤ L)
    (hB : capS ≤ capK * 2 ^ (Z * L)) (hψ1 : k + L ^ 6 ≤ ψ) (hψ2 : (k + L) ^ 2 * (Nat.sqrt capS + 1) ≤ ψ) :
    E * (k + L + KF * L ^ 2 + tSOf capS D2 K0 L + 1) ≤ E * cSOf Z D2 * ψ + cFOf E KF Z D2 K0 capK := by
  have hT := tS_le capS capK Z L D2 K0 hB
  obtain ⟨σ, hσ⟩ : ∃ s, s = Nat.sqrt capS + 1 := ⟨_, rfl⟩
  rw [← hσ] at hT hψ2
  obtain ⟨lam, hlam⟩ : ∃ x, x = Nat.clog 2 capK + 23 := ⟨_, rfl⟩
  rw [← hlam] at hT
  have hL2σ : L ^ 2 * σ ≤ ψ := le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)) hψ2
  -- the expansion of `T`'s bound
  have eT : (196608 * (lam + Z * L) * σ + 1) * (L * D2 + K0) =
      196608 * Z * D2 * (L ^ 2 * σ) + (196608 * (Z * K0 + lam * D2)) * (L * σ) + (196608 * lam * K0) * σ +
        (L * D2 + K0) := by ring
  rw [eT] at hT
  -- the `L·σ` term
  have hsmall : ∀ c : ℕ, ¬ c ≤ L → σ ≤ capK * 2 ^ (Z * c) + 1 := by
    intro c hc
    have a1 : capS ≤ capK * 2 ^ (Z * c) :=
      le_trans hB (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))))
    have := sqrt_le_self1 capS
    omega
  have t2 : (196608 * (Z * K0 + lam * D2)) * (L * σ) ≤
      ψ + (196608 * (Z * K0 + lam * D2)) * (L * (capK * 2 ^ (Z * (196608 * (Z * K0 + lam * D2))) + 1)) := by
    obtain ⟨c, hc⟩ : ∃ x, x = 196608 * (Z * K0 + lam * D2) := ⟨_, rfl⟩
    rw [← hc]
    by_cases h : c ≤ L
    · have : c * (L * σ) ≤ L * (L * σ) := Nat.mul_le_mul_right _ h
      have e : L * (L * σ) = L ^ 2 * σ := by ring
      omega
    · have a1 := hsmall c h
      have a2 : c * (L * σ) ≤ c * (L * (capK * 2 ^ (Z * c) + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ a1)
      omega
  -- bound `L` below the threshold
  have t2' : (196608 * (Z * K0 + lam * D2)) * (L * σ) ≤
      ψ + (196608 * (Z * K0 + lam * D2)) * ((196608 * (Z * K0 + lam * D2)) *
        (capK * 2 ^ (Z * (196608 * (Z * K0 + lam * D2))) + 1)) := by
    obtain ⟨c, hc⟩ : ∃ x, x = 196608 * (Z * K0 + lam * D2) := ⟨_, rfl⟩
    rw [← hc]
    by_cases h : c ≤ L
    · have : c * (L * σ) ≤ L * (L * σ) := Nat.mul_le_mul_right _ h
      have e : L * (L * σ) = L ^ 2 * σ := by ring
      omega
    · have a1 := hsmall c h
      have a2 : c * (L * σ) ≤ c * (c * (capK * 2 ^ (Z * c) + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) a1)
      omega
  -- the `σ` term
  have t3 : (196608 * lam * K0) * σ ≤ ψ + (196608 * lam * K0) * (capK * 2 ^ (Z * (196608 * lam * K0)) + 1) := by
    obtain ⟨c, hc⟩ : ∃ x, x = 196608 * lam * K0 := ⟨_, rfl⟩
    rw [← hc]
    by_cases h : c ≤ L
    · have a1 : c ≤ L ^ 2 := le_trans h (by nlinarith)
      have := Nat.mul_le_mul_right σ a1
      omega
    · have a1 := hsmall c h
      have := Nat.mul_le_mul_left c a1
      omega
  -- `L·D₂ + K₀`
  have hL6 : L ≤ ψ := by
    have : L ≤ L ^ 6 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 6 := Nat.pow_le_pow_right hL (by norm_num)
    omega
  have t4 : L * D2 ≤ D2 * ψ := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hL6
  have t1 : 196608 * Z * D2 * (L ^ 2 * σ) ≤ 196608 * Z * D2 * ψ := Nat.mul_le_mul_left _ hL2σ
  -- the rest of `m_S`
  have hx := HashSizes.exp_link E KF 0 k L ψ hE hL hψ1
  have e0 : k + L + KF * L ^ 2 + 0 * L ^ 3 + 1 = k + L + KF * L ^ 2 + 1 := by ring
  have hT2 : tSOf capS D2 K0 L ≤ cSOf Z D2 * ψ - ψ +
      ((196608 * (Z * K0 + lam * D2)) * ((196608 * (Z * K0 + lam * D2)) *
        (capK * 2 ^ (Z * (196608 * (Z * K0 + lam * D2))) + 1)) +
       (196608 * lam * K0) * (capK * 2 ^ (Z * (196608 * lam * K0)) + 1) + K0) := by
    have eS : cSOf Z D2 * ψ = 196608 * Z * D2 * ψ + D2 * ψ + 3 * ψ := by unfold cSOf; ring
    omega
  have eE : E * (k + L + KF * L ^ 2 + tSOf capS D2 K0 L + 1) =
      E * (k + L + KF * L ^ 2 + 1) + E * tSOf capS D2 K0 L := by ring
  have hETs := Nat.mul_le_mul_left E hT2
  have hψS : ψ ≤ cSOf Z D2 * ψ := Nat.le_mul_of_pos_left _ (by unfold cSOf; omega)
  have eF : cFOf E KF Z D2 K0 capK = (E * (1 + KF + 0)) ^ 2 + E +
      E * ((196608 * (Z * K0 + lam * D2)) * ((196608 * (Z * K0 + lam * D2)) *
        (capK * 2 ^ (Z * (196608 * (Z * K0 + lam * D2))) + 1)) +
       (196608 * lam * K0) * (capK * 2 ^ (Z * (196608 * lam * K0)) + 1) + K0) := by
    rw [hlam]; rfl
  have eM : E * (cSOf Z D2 * ψ - ψ + ((196608 * (Z * K0 + lam * D2)) * ((196608 * (Z * K0 + lam * D2)) *
        (capK * 2 ^ (Z * (196608 * (Z * K0 + lam * D2))) + 1)) +
       (196608 * lam * K0) * (capK * 2 ^ (Z * (196608 * lam * K0)) + 1) + K0)) =
      E * (cSOf Z D2 * ψ - ψ) + E * ((196608 * (Z * K0 + lam * D2)) * ((196608 * (Z * K0 + lam * D2)) *
        (capK * 2 ^ (Z * (196608 * (Z * K0 + lam * D2))) + 1)) +
       (196608 * lam * K0) * (capK * 2 ^ (Z * (196608 * lam * K0)) + 1) + K0) := by ring
  have eM2 : E * (cSOf Z D2 * ψ - ψ) + E * ψ = E * cSOf Z D2 * ψ := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hψS, Nat.mul_assoc]
  rw [e0] at hx
  rw [eE, eF]
  rw [eM] at hETs
  omega

/-- **The class link at `m_S`**: `K·(2^{m_S}+1)^E ≤ (K·2^{c_F + E})·classBound E_W .preprocessing n k Ψ` whenever
`E·c_S ≤ c_ψ(E_W)`, `C_D ≥ 1`, `B_S ≤ capK·2^{ZL}`. -/
theorem class_linkS (EW : Envelope) (E K KF Z D2 K0 capK CD n k L BT BS : ℕ) (hE : 1 ≤ E) (hL : 1 ≤ L)
    (hCD : 1 ≤ CD) (hn : 1 ≤ n) (hB : BS ≤ capK * 2 ^ (Z * L)) (hcpsi : E * cSOf Z D2 ≤ EW.cpsi) :
    K * (2 ^ (k + L + KF * L ^ 2 + tSOf BS D2 K0 L) + 1) ^ E ≤
      (K * 2 ^ (cFOf E KF Z D2 K0 capK + E)) * classBound EW .preprocessing n k (loadPsi CD k L BT BS) := by
  have hψ1 := HashSizes.loadPsi_ge CD k L BT BS hCD
  have hψ2 : (k + L) ^ 2 * (Nat.sqrt BS + 1) ≤ loadPsi CD k L BT BS := by
    have h1 : loadSym CD k L BS ≤ loadPsi CD k L BT BS := le_trans (le_max_left _ _) (le_max_right _ _)
    refine le_trans ?_ h1
    unfold loadSym sqrtUp
    have a1 : (k + L) ^ 2 * (Nat.sqrt BS + 1) ≤ (k + L) ^ 2 * (CD * (Nat.sqrt BS + 1 + L)) := by
      apply Nat.mul_le_mul_left
      calc Nat.sqrt BS + 1 ≤ Nat.sqrt BS + 1 + L := Nat.le_add_right _ _
        _ = 1 * (Nat.sqrt BS + 1 + L) := (one_mul _).symm
        _ ≤ CD * (Nat.sqrt BS + 1 + L) := Nat.mul_le_mul_right _ hCD
    have a2 : (k + L) ^ 2 * (CD * (Nat.sqrt BS + 1 + L)) ≤ (k + L) ^ 2 * (CD * (Nat.sqrt BS + 1 + L)) + k + L ^ 2 :=
      by omega
    calc (k + L) ^ 2 * (Nat.sqrt BS + 1) ≤ (k + L) ^ 2 * (CD * (Nat.sqrt BS + 1 + L)) + k + L ^ 2 := le_trans a1 a2
      _ = 1 * ((k + L) ^ 2 * (CD * (Nat.sqrt BS + 1 + L)) + k + L ^ 2) := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hCD
  have hx := exp_linkS E KF Z D2 K0 BS capK k L (loadPsi CD k L BT BS) hE hL hB hψ1 hψ2
  have h1 := HashSizes.pow_succ_le (k + L + KF * L ^ 2 + tSOf BS D2 K0 L) E
  have h3 : 2 ^ (E * (k + L + KF * L ^ 2 + tSOf BS D2 K0 L + 1)) ≤
      2 ^ (cFOf E KF Z D2 K0 capK + E) * 2 ^ (E * cSOf Z D2 * loadPsi CD k L BT BS) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (E * cSOf Z D2 * loadPsi CD k L BT BS) ≤ classBound EW .preprocessing n k (loadPsi CD k L BT BS) := by
    show 2 ^ (E * cSOf Z D2 * loadPsi CD k L BT BS) ≤ 2 ^ (EW.cpsi * loadPsi CD k L BT BS) * n ^ EW.Apre
    have a1 : 2 ^ (E * cSOf Z D2 * loadPsi CD k L BT BS) ≤ 2 ^ (EW.cpsi * loadPsi CD k L BT BS) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hcpsi)
    have a2 : 1 ≤ n ^ EW.Apre := Nat.one_le_pow _ _ hn
    calc 2 ^ (E * cSOf Z D2 * loadPsi CD k L BT BS) ≤ 2 ^ (EW.cpsi * loadPsi CD k L BT BS) * 1 := by
          rw [mul_one]; exact a1
      _ ≤ _ := Nat.mul_le_mul_left _ a2
  calc K * (2 ^ (k + L + KF * L ^ 2 + tSOf BS D2 K0 L) + 1) ^ E
      ≤ K * (2 ^ (cFOf E KF Z D2 K0 capK + E) * 2 ^ (E * cSOf Z D2 * loadPsi CD k L BT BS)) :=
        Nat.mul_le_mul_left _ (le_trans h1 h3)
    _ ≤ K * (2 ^ (cFOf E KF Z D2 K0 capK + E) * classBound EW .preprocessing n k (loadPsi CD k L BT BS)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
    _ = _ := by ring

end NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
