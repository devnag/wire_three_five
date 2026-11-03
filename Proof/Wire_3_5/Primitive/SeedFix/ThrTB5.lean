import Proof.Wire_3_5.Primitive.SeedFix.ThrTB4Base

/-! # THRTAIL T-B, part 5: the unit side of the THR shell (the scrub capacity)

At the master bound `Y = 2^m + 1` with the unit's measure `meas ≤ D₀·Y` (`meas_le_dim`): the unit's capacity
`cap = need(meas) + b` (`b = C_L·Y` the loop's units, THRU4's `cap := need(meas) + b`) and the unit budget
`n_U = nU(meas + cap)` are both below the scrub capacity `C·Y^D` at `D = (D₀+1)²`, `C = C₀k₁^{D₀} + k₁ + 200`,
`k₁ = D₀ + C₀(D₀+1)^{D₀} + C_L + 2` (THRU4's `need_le`, `nU_le` with `K_n, K_u ≤ C₀`, `D_n, D_u ≤ D₀`); the boot's
cost is below `200·Y`.

* `dSh`, `k1U`, `cSh`; **`unit_fits`**, **`boot_le`**.

Paper quantity of the main type: the THR writer's per-unit budget within `2^{O(m_T)}` (P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.BlockPlatform NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD

/-- The scrub capacity's exponent. -/
def dSh (D0 : ℕ) : ℕ := (D0 + 1) * (D0 + 1)

/-- The unit's base coefficient. -/
def k1U (D0 C0 CL : ℕ) : ℕ := D0 + C0 * (D0 + 1) ^ D0 + CL + 2

/-- The scrub capacity's coefficient. -/
def cSh (D0 C0 CL : ℕ) : ℕ := C0 * k1U D0 C0 CL ^ D0 + k1U D0 C0 CL + 200

theorem powY_mono {Y a b : ℕ} (hY : 1 ≤ Y) (h : a ≤ b) : Y ^ a ≤ Y ^ b := Nat.pow_le_pow_right hY h

/-- **The unit's capacity and budget within the scrub capacity.** -/
theorem unit_fits (Y D0 C0 CL meas Kn Dn Ku Du : ℕ) (need nU : ℕ → ℕ) (hY : 1 ≤ Y) (hmeas : meas ≤ D0 * Y)
    (hKn : Kn ≤ C0) (hDn : Dn ≤ D0) (hKu : Ku ≤ C0) (hDu : Du ≤ D0)
    (hneed : ∀ X, need X ≤ Kn * (X + 1) ^ Dn) (hnU : ∀ X, nU X ≤ Ku * (X + 1) ^ Du) :
    need meas + CL * Y + 1 ≤ cSh D0 C0 CL * Y ^ dSh D0 ∧
      nU (meas + (need meas + CL * Y)) + 1 ≤ cSh D0 C0 CL * Y ^ dSh D0 := by
  obtain ⟨k1, hk1⟩ : ∃ x, x = k1U D0 C0 CL := ⟨_, rfl⟩
  have hk1d : k1 = D0 + C0 * (D0 + 1) ^ D0 + CL + 2 := by rw [hk1]; rfl
  have hcS : cSh D0 C0 CL = C0 * k1 ^ D0 + k1 + 200 := by rw [hk1]; rfl
  rw [hcS]
  have hk11 : 1 ≤ k1 := by omega
  obtain ⟨P, hP⟩ : ∃ x, x = Y ^ (D0 + 1) := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := by rw [hP]; exact Nat.one_le_pow _ _ hY
  have hYP : Y ≤ P := by rw [hP]; calc Y = Y ^ 1 := (pow_one Y).symm
    _ ≤ Y ^ (D0 + 1) := powY_mono hY (by omega)
  -- the need
  have n1 : need meas ≤ C0 * (D0 + 1) ^ D0 * Y ^ D0 := by
    have h1 := hneed meas
    have h2 : meas + 1 ≤ (D0 + 1) * Y := by nlinarith
    have h3 : (meas + 1) ^ Dn ≤ ((D0 + 1) * Y) ^ D0 :=
      (Nat.pow_le_pow_left h2 Dn).trans (Nat.pow_le_pow_right (by nlinarith) hDn)
    calc need meas ≤ Kn * (meas + 1) ^ Dn := h1
      _ ≤ C0 * ((D0 + 1) * Y) ^ D0 := Nat.mul_le_mul hKn h3
      _ = C0 * (D0 + 1) ^ D0 * Y ^ D0 := by rw [mul_pow]; ring
  have n2 : C0 * (D0 + 1) ^ D0 * Y ^ D0 ≤ C0 * (D0 + 1) ^ D0 * P :=
    Nat.mul_le_mul_left _ (by rw [hP]; exact powY_mono hY (by omega))
  have hcap : need meas + CL * Y + 1 ≤ (k1 - D0) * P := by
    have e : (k1 - D0) * P = C0 * (D0 + 1) ^ D0 * P + CL * P + 2 * P := by
      rw [hk1d, show D0 + C0 * (D0 + 1) ^ D0 + CL + 2 - D0 = C0 * (D0 + 1) ^ D0 + CL + 2 by omega]; ring
    have : CL * Y ≤ CL * P := Nat.mul_le_mul_left _ hYP
    omega
  have hmc : meas + (need meas + CL * Y) + 1 ≤ k1 * P := by
    have a1 : meas ≤ D0 * P := hmeas.trans (Nat.mul_le_mul_left _ hYP)
    have e : k1 * P = D0 * P + (k1 - D0) * P := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  -- the budget
  have b1 : nU (meas + (need meas + CL * Y)) ≤ C0 * (k1 * P) ^ D0 := by
    have h1 := hnU (meas + (need meas + CL * Y))
    have h2 : (meas + (need meas + CL * Y) + 1) ^ Du ≤ (k1 * P) ^ D0 :=
      (Nat.pow_le_pow_left hmc Du).trans (Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))) hDu)
    exact h1.trans (Nat.mul_le_mul hKu h2)
  have b2 : C0 * (k1 * P) ^ D0 = C0 * k1 ^ D0 * Y ^ ((D0 + 1) * D0) := by
    rw [mul_pow, hP, ← pow_mul]; ring
  have b3 : Y ^ ((D0 + 1) * D0) ≤ Y ^ dSh D0 := powY_mono hY (by unfold dSh; nlinarith)
  have b4 : P ≤ Y ^ dSh D0 := by rw [hP]; exact powY_mono hY (by unfold dSh; nlinarith)
  have b5 : 1 ≤ Y ^ dSh D0 := Nat.one_le_pow _ _ hY
  have e1 : (C0 * k1 ^ D0 + k1 + 200) * Y ^ dSh D0 = C0 * k1 ^ D0 * Y ^ dSh D0 + k1 * Y ^ dSh D0 + 200 * Y ^ dSh D0 := by
    ring
  have c1 : C0 * k1 ^ D0 * Y ^ ((D0 + 1) * D0) ≤ C0 * k1 ^ D0 * Y ^ dSh D0 := Nat.mul_le_mul_left _ b3
  have c2 : (k1 - D0) * P ≤ k1 * Y ^ dSh D0 := Nat.mul_le_mul (by omega) b4
  constructor
  · omega
  · omega

/-- The boot's cost at the master bound. -/
theorem boot_le (w : List Bool) (n Y : ℕ) (hw : w.length ≤ Y) (hn : n + 1 ≤ Y) : bootCost w n 0 0 ≤ 200 * Y := by
  have hbn := CopyNat.natBitLength_le_self_succ n
  have b00 := UnaryCalc.poly_cost_polyBounded 0 0 n
  unfold ValidatorPolynomialDomination.PolyBounded at b00
  have e00 : UnaryCalc.polyCoefficient 0 0 * (n + 1) ^ (0 + 1) = 13 * (n + 1) := by
    simp [UnaryCalc.polyCoefficient]
  have v00 : UnaryCalc.value 0 0 n = 0 := by simp [UnaryCalc.value]
  unfold bootCost
  rw [v00]
  omega

end NearCubicWires.WireExponent3_5.PrimT.ThrTB
