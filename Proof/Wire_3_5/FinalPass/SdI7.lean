import Proof.Wire_3_5.FinalPass.SdI6

/-! # S4 (the seeds phase), part 56: the seeds phase's constants (P3:3170-3178)

The register capacity `Kc·(|fpIn|+1)^{Dc}`, the per-seed bound `Ct·(|fpIn|+1)^{Dt}`, the per-point bound
`Cp·(n+1)^{Dp}` and the overhead `Co·(|fpIn|+1)^{Do}`, with the constants from the sizes' polynomial (`KX`, `ZX`), the
tables writer's shell constants and the SYM evaluator's number count only. **`bud_poly`**: the writer's budget
`≤ budC·(|fpIn|+1)^{budD}` (the shell's cost at the writer's dimension `2^m + 1 ≤ 5(|fpIn|+1)^4`); **`cap_poly`**,
**`ov_poly`**: the capacity and the overhead against their polynomials.

Paper quantity of the main type: the seeds phase's time and space, polynomial in the input (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.PrimAsm.ShellT NearCubicWires.BlockPlatform

/-! ## The writer's budget -/

/-- The writer's base. -/
def budB (cX Cc Dcc : ℕ) : ℕ := 16 * cX + Cc * 129 ^ Dcc + 8

/-- The writer's base exponent. -/
def budE (ZX Dcc : ℕ) : ℕ := ZX + Dcc + 4

/-- The writer's power. -/
def budS (D DL : ℕ) : ℕ := EcT D 1 1 DL + DL + D

/-- **The writer's budget's coefficient.** -/
def budC (D C DL CL cr cX Cc Dcc : ℕ) : ℕ :=
  (2 * KcT D C 1 64 1 (cr + 18) cr DL CL 0 + 4 * CL * C + 10 * CL) * budB cX Cc Dcc ^ budS D DL

/-- **The writer's budget's exponent.** -/
def budD (D DL ZX Dcc : ℕ) : ℕ := budE ZX Dcc * budS D DL

theorem bud_poly (w : List Bool) (n D C cc cr m DL CL nU X Fn Q cX ZX Cc Dcc : ℕ)
    (hR : nU + 1 ≤ UnaryCalc.value D C (2 ^ m)) (hw : w.length ≤ 16 * X) (hX : X ≤ cX * (Fn + 1) ^ ZX)
    (hn : n ≤ Fn) (hcc : cc ≤ Cc * (129 * (Fn + 1)) ^ Dcc) (hm : 2 ^ m ≤ Q * Q * ((n + 2) * (n + 2))) (hQ : Q ≤ Fn) :
    2 * shellCostG w n D C 1 64 cc 1 (cr + 18) (TabW.c2Of cr n) m DL CL nU + 2 ≤
      budC D C DL CL cr cX Cc Dcc * (Fn + 1) ^ budD D DL ZX Dcc := by
  have h := TabW.bud_le w n D C cc cr m DL CL nU hR
  have hz : 1 ≤ Fn + 1 := by omega
  have hE1 : ZX ≤ budE ZX Dcc := by unfold budE; omega
  have hE2 : Dcc ≤ budE ZX Dcc := by unfold budE; omega
  have hE4 : 4 ≤ budE ZX Dcc := by unfold budE; omega
  have hXe : X ≤ cX * (Fn + 1) ^ budE ZX Dcc := hX.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hz hE1))
  have hne : n ≤ (Fn + 1) ^ budE ZX Dcc := by
    have := Nat.le_self_pow (show budE ZX Dcc ≠ 0 by omega) (Fn + 1); omega
  have hcce : cc ≤ Cc * 129 ^ Dcc * (Fn + 1) ^ budE ZX Dcc := by
    refine hcc.trans ?_
    rw [mul_pow, ← mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hz hE2)
  have hz4 : (Fn + 1) ^ 4 ≤ (Fn + 1) ^ budE ZX Dcc := Nat.pow_le_pow_right hz hE4
  have hq : Q * Q * ((n + 2) * (n + 2)) ≤ (Fn + 1) * (Fn + 1) * ((2 * (Fn + 1)) * (2 * (Fn + 1))) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.mul_le_mul (by omega) (by omega))
  have e4 : (Fn + 1) * (Fn + 1) * ((2 * (Fn + 1)) * (2 * (Fn + 1))) = 4 * (Fn + 1) ^ 4 := by ring
  have he1 : 1 ≤ (Fn + 1) ^ budE ZX Dcc := Nat.one_le_pow _ _ hz
  -- the base `B`
  obtain ⟨B, hBd⟩ : ∃ B, B = budB cX Cc Dcc * (Fn + 1) ^ budE ZX Dcc := ⟨_, rfl⟩
  have eB : B = 16 * (cX * (Fn + 1) ^ budE ZX Dcc) + Cc * 129 ^ Dcc * (Fn + 1) ^ budE ZX Dcc +
      8 * (Fn + 1) ^ budE ZX Dcc := by rw [hBd]; unfold budB; ring
  have hB1 : 1 ≤ B := by omega
  have hwB : w.length + n + cc + 2 ≤ B := by omega
  have hVB : 2 ^ m + 1 ≤ B := by omega
  have hVD : UnaryCalc.value D C (2 ^ m) ≤ C * B ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hVB _)
  have hVL : UnaryCalc.value DL CL (2 ^ m) ≤ CL * B ^ DL := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hVB _)
  have hS1 : B ^ EcT D 1 1 DL ≤ B ^ budS D DL := Nat.pow_le_pow_right hB1 (by unfold budS; omega)
  have hS2 : B ^ DL * B ^ D ≤ B ^ budS D DL := by
    rw [← pow_add]; exact Nat.pow_le_pow_right hB1 (by unfold budS; omega)
  have hS3 : B ^ DL ≤ B ^ budS D DL := Nat.pow_le_pow_right hB1 (by unfold budS; omega)
  have p1 : (w.length + n + cc + 2) ^ EcT D 1 1 DL ≤ B ^ EcT D 1 1 DL := Nat.pow_le_pow_left hwB _
  have p2 : (2 ^ m + 1) ^ EcT D 1 1 DL ≤ B ^ EcT D 1 1 DL := Nat.pow_le_pow_left hVB _
  have hlast : UnaryCalc.value DL CL (2 ^ m) * (2 * nU + 2 * UnaryCalc.value D C (2 ^ m) + 10) ≤
      4 * CL * C * B ^ budS D DL + 10 * CL * B ^ budS D DL := by
    calc _ ≤ (CL * B ^ DL) * (4 * (C * B ^ D) + 10) := Nat.mul_le_mul hVL (by omega)
      _ = 4 * CL * C * (B ^ DL * B ^ D) + 10 * CL * B ^ DL := by ring
      _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ hS2) (Nat.mul_le_mul_left _ hS3)
  have hK1 := Nat.mul_le_mul_left (KcT D C 1 64 1 (cr + 18) cr DL CL 0) (p1.trans hS1)
  have hK2 := Nat.mul_le_mul_left (KcT D C 1 64 1 (cr + 18) cr DL CL 0) (p2.trans hS1)
  have eP : B ^ budS D DL = budB cX Cc Dcc ^ budS D DL * (Fn + 1) ^ budD D DL ZX Dcc := by
    rw [hBd, mul_pow, ← pow_mul]; rfl
  have eC : budC D C DL CL cr cX Cc Dcc * (Fn + 1) ^ budD D DL ZX Dcc =
      2 * (KcT D C 1 64 1 (cr + 18) cr DL CL 0 * B ^ budS D DL) + 4 * CL * C * B ^ budS D DL +
        10 * CL * B ^ budS D DL := by
    rw [eP]; unfold budC; ring
  rw [eC]
  omega

/-! ## The capacity and the overhead -/

theorem cap_poly (X Fn cX ZX nn : ℕ) (hX : X ≤ cX * (Fn + 1) ^ ZX) (hZ : 1 ≤ ZX) :
    capNeed X Fn + nn ≤ (10000 * cX ^ 3 + 106 + nn) * (Fn + 1) ^ (3 * ZX) := by
  unfold capNeed
  have hz : 1 ≤ Fn + 1 := by omega
  have hy : 1 ≤ (Fn + 1) ^ ZX := Nat.one_le_pow _ _ hz
  have hX3 : X * X * X ≤ cX ^ 3 * ((Fn + 1) ^ ZX) ^ 3 := by
    calc X * X * X ≤ (cX * (Fn + 1) ^ ZX) * (cX * (Fn + 1) ^ ZX) * (cX * (Fn + 1) ^ ZX) :=
          Nat.mul_le_mul (Nat.mul_le_mul hX hX) hX
      _ = _ := by ring
  have hz1 : Fn + 1 ≤ (Fn + 1) ^ ZX := Nat.le_self_pow (by omega) _
  have hF : Fn * (4 * (Fn * Fn) + 2) ≤ 6 * ((Fn + 1) ^ ZX) ^ 3 := by
    calc Fn * (4 * (Fn * Fn) + 2) ≤ 6 * ((Fn + 1) * (Fn + 1) * (Fn + 1)) := by nlinarith
      _ ≤ 6 * ((Fn + 1) ^ ZX * (Fn + 1) ^ ZX * (Fn + 1) ^ ZX) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul hz1 hz1) hz1)
      _ = _ := by ring
  have hy3 : 1 ≤ ((Fn + 1) ^ ZX) ^ 3 := Nat.one_le_pow _ _ hy
  rw [pow_mul']
  have e : (10000 * cX ^ 3 + 106 + nn) * ((Fn + 1) ^ ZX) ^ 3 =
      10000 * (cX ^ 3 * ((Fn + 1) ^ ZX) ^ 3) + 106 * ((Fn + 1) ^ ZX) ^ 3 + nn * ((Fn + 1) ^ ZX) ^ 3 := by ring
  rw [e]
  have := Nat.le_mul_of_pos_right nn hy3
  omega

theorem ov_poly (pc bud bA X Fn cX ZX bC bD cap Kc Dc nn : ℕ) (hp : pc ≤ 10000 * (X * X))
    (hX : X ≤ cX * (Fn + 1) ^ ZX) (hb : bud ≤ bC * (Fn + 1) ^ bD) (hA : bA ≤ (2400 + 3 * nn) * (cap + 1))
    (hc : cap = Kc * (Fn + 1) ^ Dc) :
    pc + 1 + bud + 1 + (bA + 1) ≤
      (10000 * cX ^ 2 + bC + (2400 + 3 * nn) * (Kc + 1) + 3) * (Fn + 1) ^ (2 * ZX + bD + Dc) := by
  have hz : 1 ≤ Fn + 1 := by omega
  obtain ⟨z, hzd⟩ : ∃ z, z = (Fn + 1) ^ (2 * ZX + bD + Dc) := ⟨_, rfl⟩
  have hz1 : 1 ≤ z := by rw [hzd]; exact Nat.one_le_pow _ _ hz
  have h1 : X * X ≤ cX ^ 2 * z := by
    calc X * X ≤ (cX * (Fn + 1) ^ ZX) * (cX * (Fn + 1) ^ ZX) := Nat.mul_le_mul hX hX
      _ = cX ^ 2 * (Fn + 1) ^ (2 * ZX) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by rw [hzd]; exact Nat.pow_le_pow_right hz (by omega))
  have h2 : bud ≤ bC * z := hb.trans (Nat.mul_le_mul_left _ (by rw [hzd]; exact Nat.pow_le_pow_right hz (by omega)))
  have h3 : cap + 1 ≤ (Kc + 1) * z := by
    rw [hc]
    have : (Fn + 1) ^ Dc ≤ z := by rw [hzd]; exact Nat.pow_le_pow_right hz (by omega)
    have := Nat.mul_le_mul_left Kc this
    rw [Nat.add_mul, one_mul]
    omega
  have h4 := Nat.mul_le_mul_left (2400 + 3 * nn) h3
  have e : (10000 * cX ^ 2 + bC + (2400 + 3 * nn) * (Kc + 1) + 3) * z =
      10000 * (cX ^ 2 * z) + bC * z + (2400 + 3 * nn) * ((Kc + 1) * z) + 3 * z := by ring
  rw [← hzd, e]
  have := Nat.mul_le_mul_left 10000 h1
  omega

end NearCubicWires.WireExponent3_5.FinalPass.Sd

