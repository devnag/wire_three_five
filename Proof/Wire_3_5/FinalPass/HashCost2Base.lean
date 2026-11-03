import Proof.Wire_3_5.FinalPass.HashCost1Base
import Proof.Wire_3_5.FinalPass.HashOccBase
import Proof.Wire_3_5.FinalPass.SymCost3

/-! # The HASH child's cost, part 2: the exponents below the pad (the arithmetic)

P3:3098-3107 (the pad `2^ρ`, `ρ ≥ n − k + d_A L`; the load condition `max{Ψ_i, Ψ_aux} ≤ c₀(n−k)`) at a HASH call:
with `S = S_aux = k + L² + (k+L³)L²(k+L)` (`C_D·S = Ψ_aux ≤ ψ ≤ n`), every exponent of the HASH child's steps is
`O(S)` plus the capacity's `⌊n/16⌋ + d_C L²` plus `O(L)`: the fixed fields `e_F`, the charged occurrences
`e_O = C₁S`, the printed word `e_W`, the Hb size `e_S`. Under the floor `costCDH ≤ C_D` (fixed before `F`)
and `d_A ≥ dAH` (fixed before `F`), the conditions of `kch_pow` (at `d_A − 1`) and the HASH-specific
budgets (the Hb prep `2^{3e_C+38}`, the cells `2^{2e_C+2}`, the word `2^{e_W+13}`, the capacity floor
`2^{32}(hbS+1)^8 ≤ 2^{e_C}`) hold.

* `cF1`, `c0F`, `hashB`, `costCDH`, `dAH`; **`hcostH_exp`**.

Paper quantity of the main type: the HASH child's step exponents against the pad. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.SymFr

/-- The fixed fields' additive constant. -/
def c0F (c : SymC) : ℕ := c.dQ + c.dH + c.dP + c.dD + 10

/-- **The HASH pad's exponent constant** (`dAH ≤ d_A`). -/
def dAH (c : SymC) (Cw ex : ℕ) : ℕ :=
  1 + Cw + 1034023 + ex * (c.dP + 2) + ex * (c.eP + 1) + 41 * (c.eH + c.eP) + 41 * c0F c + 200

/-- **The exponent conditions at a HASH call** (the three of `kch_pow` at `d_A − 1`, the word below the capacity,
the HASH budgets, the capacity floor). -/
theorem hcostH_exp (n K L S CD dC dA eH eP dP C1 cF cW cS Cw ex c0 eF eW eSx : ℕ) (hL1 : 1 ≤ L)
    (hKS : K ≤ S) (hLS : L * L ≤ S) (hAux : CD * S ≤ n)
    (hF : eF ≤ (1 + 8 * cF) * S + (eH + eP) * L + c0) (hW : eW ≤ (2 + 8 * cW) * S)
    (hSx : eSx ≤ (2 + 8 * cS) * S)
    (hCD : 64 * (11 * dC + 41 * (1 + 8 * cF) + 11 * C1 + 4 * (2 + 8 * cW) + (16 + 64 * cS) + 64) ≤ CD)
    (hdA : 1 + Cw + 1034023 + ex * (dP + 2) + ex * (eP + 1) + 41 * (eH + eP) + 41 * c0 + 200 ≤ dA) :
    3 * ((n / 16 + dC * (L * L)) + (3 * eF + C1 * S + eW + 9)) + 27 ≤ (n - K) + (dA - 1) * L ∧
      8 * (C1 * S) + 32 * eF + 8 * (n / 16 + dC * (L * L)) + 94 ≤ (n - K) + (dA - 1) * L ∧
      Cw + 1034023 + ex * (dP + 2 + (eP + 1) * L) ≤ (dA - 1) * L ∧
      eW + 1 ≤ n / 16 + dC * (L * L) ∧
      3 * (n / 16 + dC * (L * L)) + 45 ≤ (n - K) + dA * L ∧
      2 * (n / 16 + dC * (L * L)) + 9 ≤ (n - K) + dA * L ∧
      eW + 20 ≤ (n - K) + dA * L ∧
      32 + 8 * (eSx + 1) ≤ n / 16 + dC * (L * L) := by
  obtain ⟨B, hBd⟩ : ∃ B, B = 11 * dC + 41 * (1 + 8 * cF) + 11 * C1 + 4 * (2 + 8 * cW) + (16 + 64 * cS) + 64 := ⟨_, rfl⟩
  rw [← hBd] at hCD
  have hBS : 64 * (B * S) ≤ n := by
    have h1 : 64 * B * S ≤ CD * S := Nat.mul_le_mul_right _ hCD
    have e : 64 * B * S = 64 * (B * S) := by ring
    omega
  have eB : B * S = 11 * (dC * S) + 41 * ((1 + 8 * cF) * S) + 11 * (C1 * S) + 4 * ((2 + 8 * cW) * S) +
      (16 + 64 * cS) * S + 64 * S := by rw [hBd]; ring
  have hdCL : dC * (L * L) ≤ dC * S := Nat.mul_le_mul_left _ hLS
  have hL1S : 1 ≤ S := le_trans (Nat.mul_le_mul hL1 hL1) hLS
  -- the pad's `L` coefficient
  obtain ⟨dA', hdA'⟩ : ∃ d, d = dA - 1 := ⟨_, rfl⟩
  have hdA1 : 1 + Cw + 1034023 + ex * (dP + 2) + ex * (eP + 1) + 41 * (eH + eP) + 41 * c0 + 200 ≤ dA' + 1 := by omega
  have g1 : (Cw + 1034023 + ex * (dP + 2) + ex * (eP + 1) + 41 * (eH + eP) + 41 * c0 + 200) * L ≤ dA' * L :=
    Nat.mul_le_mul_right _ (by omega)
  have g2 : (Cw + 1034023 + ex * (dP + 2) + ex * (eP + 1) + 41 * (eH + eP) + 41 * c0 + 200) * L =
      (Cw + 1034023) * L + ex * (dP + 2) * L + ex * ((eP + 1) * L) + 41 * ((eH + eP) * L) + 41 * c0 * L + 200 * L := by
    ring
  have g3 : Cw + 1034023 ≤ (Cw + 1034023) * L := Nat.le_mul_of_pos_right _ hL1
  have g4 : ex * (dP + 2) ≤ ex * (dP + 2) * L := Nat.le_mul_of_pos_right _ hL1
  have g5 : 41 * c0 ≤ 41 * c0 * L := Nat.le_mul_of_pos_right _ hL1
  have g6 : ex * (dP + 2 + (eP + 1) * L) = ex * (dP + 2) + ex * ((eP + 1) * L) := by ring
  have g7 : dA * L = dA' * L + L := by
    have : dA = dA' + 1 := by omega
    rw [this]; ring
  have g8 : (eH + eP) * L ≤ 41 * ((eH + eP) * L) := by omega
  have hmul : 3 * (1 + 8 * cF) * S ≤ 41 * ((1 + 8 * cF) * S) := by
    have e : 3 * (1 + 8 * cF) * S = 3 * ((1 + 8 * cF) * S) := by ring
    omega
  rw [g6, ← hdA']
  refine ⟨?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have : 8 * ((2 + 8 * cS) * S) = (16 + 64 * cS) * S := by ring
    omega

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
