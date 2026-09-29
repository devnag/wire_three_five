import Proof.Wire_3_5.Primitive.Writers.SFCost1

/-! # polynomial bounds on the SeedFix stages' step counts, part 2 (the record loop, the coefficients)

`loopCost` (the elimination's record loop: labels, targets, the constraint rows, the clear) at every argument `≤ q`,
the prefix length not assumed `≤ 2h·ℓ` (`passesCost_le'`, `rowCost_le'`, `consCost_le'`, `recCost_le'`), and
`coefCost` (the coefficient writer: `|bs| ≤ q`, `R₂, e ≤ q`).

Paper quantity: none (the step counts of `samp:seed`'s machines, P3:3034-3038). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SFCost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix

theorem pw (Q a b : ℕ) (hQ : 1 ≤ Q) (h : a ≤ b) : Q ^ a ≤ Q ^ b := Nat.pow_le_pow_right hQ h

theorem passesCost_le' (ℓ plen n q : ℕ) (hl : ℓ ≤ q) (hp : plen ≤ q) (hn : n ≤ (q + 1) ^ 2) :
    passesCost ℓ plen n ≤ 54 * (q + 1) ^ 3 := by
  unfold passesCost
  have hA := phACost_le ℓ q hl
  have hB := phBCost_le ℓ q hl
  rw [pow_one] at hA hB
  have h1 : plen * (phACost ℓ + 2) ≤ (q + 1) * (16 * (q + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (n - plen) * (phBCost ℓ + 2) ≤ (q + 1) ^ 2 * (16 * (q + 1)) :=
    Nat.mul_le_mul (le_trans (Nat.sub_le _ _) hn) (by omega)
  have e1 : (q + 1) * (16 * (q + 1)) = 16 * (q + 1) ^ 2 := by ring
  have e2 : (q + 1) ^ 2 * (16 * (q + 1)) = 16 * (q + 1) ^ 3 := by ring
  have p23 := pw (q + 1) 2 3 (by omega) (by norm_num)
  have p03 : 1 ≤ (q + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

theorem rowCost_le' (ℓ plen n q : ℕ) (hl : ℓ ≤ q) (hp : plen ≤ q) (hn : n ≤ (q + 1) ^ 2) :
    rowCost ℓ plen n ≤ 140 * (q + 1) ^ 3 := by
  unfold rowCost
  have h1 := passesCost_le' ℓ plen n q hl hp hn
  rw [lfsr_eq]
  have p13 := pw (q + 1) 1 3 (by omega) (by norm_num)
  rw [pow_one] at p13
  omega

theorem consCost_le' (ℓ twoH k plen q : ℕ) (hl : ℓ ≤ q) (ht : twoH ≤ q) (hk : k ≤ q) (hp : plen ≤ q) :
    consCost ℓ twoH k plen ≤ 720 * (q + 1) ^ 4 := by
  unfold consCost
  have hn : twoH * ℓ ≤ (q + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h1 := tableCost_le ℓ twoH (q + 1) (by omega) (by omega) (by omega)
  have h2 := rowCost_le' ℓ plen (twoH * ℓ) q hl hp hn
  have h3 : k * (rowCost ℓ plen (twoH * ℓ) + 2) ≤ (q + 1) * (142 * (q + 1) ^ 3) := Nat.mul_le_mul (by omega) (by
    have := Nat.one_le_pow 3 (q + 1) (by omega)
    omega)
  have e3 : (q + 1) * (142 * (q + 1) ^ 3) = 142 * (q + 1) ^ 4 := by ring
  have p34 := pw (q + 1) 3 4 (by omega) (by norm_num)
  have p14 := pw (q + 1) 1 4 (by omega) (by norm_num)
  rw [pow_one] at p14
  omega

theorem recCost_le' (ℓ twoH k plen q : ℕ) (hl : ℓ ≤ q) (ht : twoH ≤ q) (hk : k ≤ q) (hp : plen ≤ q) :
    recCost ℓ twoH k plen ≤ 753 * (q + 1) ^ 4 := by
  unfold recCost labCost tgtCost clrCost
  have h1 := consCost_le' ℓ twoH k plen q hl ht hk hp
  have p14 := pw (q + 1) 1 4 (by omega) (by norm_num)
  rw [pow_one] at p14
  omega

/-- **The record loop's cost.** -/
theorem loopCost_le (ℓ twoH k plen n q : ℕ) (hl : ℓ ≤ q) (ht : twoH ≤ q) (hk : k ≤ q) (hp : plen ≤ q) (hn : n ≤ q) :
    loopCost ℓ twoH k plen n ≤ 756 * (q + 1) ^ 5 := by
  unfold loopCost
  have h1 := recCost_le' ℓ twoH k plen q hl ht hk hp
  have h2 : n * (recCost ℓ twoH k plen + 2) ≤ (q + 1) * (755 * (q + 1) ^ 4) := Nat.mul_le_mul (by omega) (by
    have := Nat.one_le_pow 4 (q + 1) (by omega)
    omega)
  have e2 : (q + 1) * (755 * (q + 1) ^ 4) = 755 * (q + 1) ^ 5 := by ring
  have p05 : 1 ≤ (q + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  omega

theorem betaCost_le (bs : List Bool) (R2 i q : ℕ) (hR : R2 ≤ q) : betaCost bs R2 i ≤ 8 * q + 10 := by
  unfold betaCost
  split_ifs <;> omega

/-- **The coefficient writer's cost.** -/
theorem coefCost_le (bs : List Bool) (R2 e q : ℕ) (hb : bs.length ≤ q) (hR : R2 ≤ q) (he : e ≤ q) :
    coefCost bs R2 e ≤ 66 * (q + 1) ^ 2 := by
  unfold coefCost
  have hs : ((List.range (bs.length - 0)).map (fun i => betaCost bs R2 (0 + i) + 2)).sum ≤ q * (8 * q + 12) := by
    have := List.sum_le_card_nsmul ((List.range (bs.length - 0)).map (fun i => betaCost bs R2 (0 + i) + 2))
      (8 * q + 12) (fun y hy => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
        have := betaCost_le bs R2 (0 + i) q hR
        omega)
    simp only [List.length_map, List.length_range, smul_eq_mul, Nat.sub_zero] at this
    exact le_trans this (Nat.mul_le_mul_right _ hb)
  have e2 : (q + 1) ^ 2 = q * q + 2 * q + 1 := by ring
  nlinarith

end NearCubicWires.WireExponent3_5.PrimAsm.SFCost
