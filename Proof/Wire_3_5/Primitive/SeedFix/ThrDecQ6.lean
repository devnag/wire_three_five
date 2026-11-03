import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5Base
import Proof.Wire_3_5.Primitive.Writers.SymCosts
import Proof.Wire_3_5.Primitive.Writers.ThrN2

/-! # THR decode front, packaging part 6: the front's cost at its virtual capacity

`front_run`'s cost bound (the register programs at `c₀`, `T`'s and `N`'s docks at the values `≤ c₀`, the post program)
is at most `fK T N · (c₀+1)^{fD T N}`, where `fK`, `fD` depend on the docked machines only (`T`, `N`: from `l`).

* `fK`, `fD`; **`front_cost_le`**.

Paper quantity of the main type: the decode front's time within a polynomial of its capacity (P3:2597-2599). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm

section Cost
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)

/-- The front's cost coefficient (from the docked machines). -/
def fK : ℕ := 700000 * (N.Dn + 2) + T.Cc + N.Cc

/-- The front's cost degree (from the docked machines). -/
def fD : ℕ := 3 + T.Dc + N.Dc

theorem pow_fD_ge (c k : ℕ) (hk : k ≤ fD T N) : (c + 1) ^ k ≤ (c + 1) ^ fD T N :=
  Nat.pow_le_pow_right (by omega) hk

theorem cube_le (c : ℕ) : (c + 1) * ((c + 1) * (c + 1)) ≤ (c + 1) ^ fD T N := by
  have h := pow_fD_ge T N c 3 (by unfold fD; omega)
  have e : (c + 1) ^ 3 = (c + 1) * ((c + 1) * (c + 1)) := by ring
  omega

/-- **The front's cost** at its virtual capacity `c`, from the values' fits. -/
theorem front_cost_le (n a nc Kb cr fe c TOT V capT ncar Llen uLen : ℕ) (ha : a ≤ 4) (hnc : nc ≤ 2)
    (hP : n + Kb ≤ c) (h3 : (fe + 4) * (n + 3) + 2 * cr + 20 ≤ c) (hT : TOT ≤ c) (hV : V + n + capT + ncar ≤ c)
    (hL : Llen ≤ uLen) (hu : uLen ≤ c) :
    W1Cost n a nc Kb cr fe c TOT V capT ncar N.Dn + 1 + (T.cost V + 1 + N.cost (n + V + capT) + 2) + 1 +
      (postCost c Llen uLen + 1) ≤ fK T N * (c + 1) ^ fD T N := by
  obtain ⟨B, hB⟩ : ∃ B, B = (c + 1) ^ fD T N := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (c + 2) * (c + 2) := ⟨_, rfl⟩
  have hsq : UnaryPow.sq c = 200 * Q := by rw [hQ]; unfold UnaryPow.sq; ring
  have r1 := SymSizes.reqParseCost_le n a nc Kb c (by omega) ha (by omega) (by omega)
  have r2 := ThrNums.starCost_le c n cr fe h3
  have r3 := SymSizes.fbCost_le c
  rw [← hQ] at r1 r3
  have hcube := cube_le T N c
  rw [← hB] at hcube
  have hQB : Q ≤ 4 * B := by
    have : Q ≤ 4 * ((c + 1) * (c + 1)) := by rw [hQ]; nlinarith
    have : (c + 1) * (c + 1) ≤ (c + 1) * ((c + 1) * (c + 1)) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hcB : c + 1 ≤ B := by
    have : c + 1 ≤ (c + 1) * ((c + 1) * (c + 1)) := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have bT : T.cost V ≤ T.Cc * B := by
    have h := T.cost_poly V
    unfold ValidatorPolynomialDomination.PolyBounded at h
    have h2 : (V + 1) ^ T.Dc ≤ (c + 1) ^ T.Dc := Nat.pow_le_pow_left (by omega) _
    have h3 := pow_fD_ge T N c T.Dc (by unfold fD; omega)
    rw [← hB] at h3
    exact h.trans (Nat.mul_le_mul_left _ (h2.trans h3))
  have bN : N.cost (n + V + capT) ≤ N.Cc * B := by
    have h := N.cost_poly (n + V + capT)
    unfold ValidatorPolynomialDomination.PolyBounded at h
    have h2 : (n + V + capT + 1) ^ N.Dc ≤ (c + 1) ^ N.Dc := Nat.pow_le_pow_left (by omega) _
    have h3 := pow_fD_ge T N c N.Dc (by unfold fD; omega)
    rw [← hB] at h3
    exact h.trans (Nat.mul_le_mul_left _ (h2.trans h3))
  have bL : (Llen + 1) * (10 * UnaryPow.sq c) ≤ 8000 * B := by
    have h1 : (Llen + 1) * (10 * UnaryPow.sq c) ≤ (c + 1) * (2000 * Q) := by
      rw [hsq]; nlinarith
    have h2 : (c + 1) * Q ≤ 4 * ((c + 1) * ((c + 1) * (c + 1))) := by rw [hQ]; nlinarith
    have e : (c + 1) * (2000 * Q) = 2000 * ((c + 1) * Q) := by ring
    omega
  have bD : (N.Dn + 1) * (4 * UnaryPow.sq c) ≤ 3200 * ((N.Dn + 1) * B) := by
    rw [hsq]
    have : (N.Dn + 1) * Q ≤ (N.Dn + 1) * (4 * B) := Nat.mul_le_mul_left _ hQB
    have e1 : (N.Dn + 1) * (4 * (200 * Q)) = 800 * ((N.Dn + 1) * Q) := by ring
    have e2 : (N.Dn + 1) * (4 * B) = 4 * ((N.Dn + 1) * B) := by ring
    omega
  have eK : fK T N * B = 700000 * ((N.Dn + 1) * B) + 700000 * B + T.Cc * B + N.Cc * B := by unfold fK; ring
  rw [← hB, eK]
  unfold W1Cost tNCost tACost finCost postCost
  omega

end Cost

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
