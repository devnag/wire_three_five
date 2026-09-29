import Proof.Wire_3_5.Primitive.SeedFix.NwB12
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ6

/-! # NW phase (b), part 13: phase (b)'s time, polynomial in the virtual capacity

**`b_cost_le`**: `b_run`'s step count (the two register programs at `c`, the docks at `V_d ≤ c`) is at most
`bKc·(3c+3)^{fD}` with `bKc = 10^7(J + D_n + 2) + C_T + C_N`, `fD = 3 + D_T + D_N` (on `l` alone).

Paper quantity of the main type: phase (b)'s time, polynomial in its capacity (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

theorem sq_eq (c : ℕ) : UnaryPow.sq c = 200 * ((c + 2) * (c + 2)) := by unfold UnaryPow.sq; ring

theorem wa1_le (c vN vM vE vT n a nc wl cr fe kh feL : ℕ) (hv : vN + vM + vE + vT ≤ 5 * c) (hn : n ≤ c)
    (ha : a ≤ 4) (hnc : nc ≤ 2) (hw : wl ≤ c) (h3 : (fe + 4) * (n + 3) + 2 * cr + 20 ≤ c) (hk : kh + feL ≤ 2 * c) :
    wa1Cost c vN vM vE vT n a nc wl cr fe kh feL ≤ 20000 * ((c + 2) * (c + 2)) := by
  have r1 := SymSizes.reqParseCost_le n a nc wl c hn ha (by omega) hw
  have r2 := ThrNums.starCost_le c n cr fe h3
  have hq : c ≤ (c + 2) * (c + 2) := by nlinarith
  unfold wa1Cost ThrDecF.tACost
  rw [sq_eq] at r2 ⊢
  omega

theorem wa2_le (c n cr t sp L tv ncar capT Dn J : ℕ) (hc1 : 1 ≤ c) (hn : n ≤ c) (hcr : cr ≤ c) (ht : t ≤ J * c + J + 1)
    (hsp : sp ≤ c) (hL : L ≤ c) (htv : tv ≤ c) (hnc : ncar ≤ c) (hcT : capT ≤ c) :
    wa2Cost c n cr t sp L tv ncar capT Dn ≤ 1000000 * ((J + Dn + 2) * ((c + 2) * ((c + 2) * (c + 2)))) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (c + 2) * (c + 2) := ⟨_, rfl⟩
  obtain ⟨C3, hC3⟩ : ∃ C, C = (c + 2) * Q := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = J + Dn + 2 := ⟨_, rfl⟩
  have hq : c ≤ Q := by rw [hQ]; nlinarith
  have hq1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQC : Q ≤ C3 := by rw [hC3]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hCK : C3 ≤ K * C3 := Nat.le_mul_of_pos_left _ (by omega)
  have q1 : t + 5 ≤ K * (c + 2) := by rw [hK]; nlinarith
  have p1 : (t + 5) * (40 * (200 * Q)) ≤ 8000 * (K * C3) := by
    have := Nat.mul_le_mul q1 (le_refl (40 * (200 * Q)))
    have e : K * (c + 2) * (40 * (200 * Q)) = 8000 * (K * C3) := by rw [hC3]; ring
    omega
  have p2 : ((c + 2) * 200 + 1500) * (200 * Q) ≤ 340000 * C3 := by
    have := Nat.mul_le_mul (show (c + 2) * 200 + 1500 ≤ 1700 * (c + 2) by omega) (le_refl (200 * Q))
    have e : 1700 * (c + 2) * (200 * Q) = 340000 * C3 := by rw [hC3]; ring
    omega
  have p3 : (Dn + 1) * (4 * (200 * Q)) ≤ 800 * (K * C3) := by
    have := Nat.mul_le_mul (show Dn + 1 ≤ K by omega) (show 4 * (200 * Q) ≤ 800 * C3 by omega)
    have e : K * (800 * C3) = 800 * (K * C3) := by ring
    omega
  have e0 : (J + Dn + 2) * ((c + 2) * ((c + 2) * (c + 2))) = K * C3 := by rw [hK, hC3, hQ]
  rw [e0]
  unfold wa2Cost TS4.capTCost
  rw [sq_eq, ← hQ]
  omega

theorem wb_le (c vN vM vE vT V : ℕ) (hv : vN + vM + vE + vT + V ≤ 5 * c) :
    wbCost c vN vM vE vT V ≤ 500000 * ((c + 2) * (c + 2)) := by
  have hq : c ≤ (c + 2) * (c + 2) := by nlinarith
  have hq1 : 1 ≤ (c + 2) * (c + 2) := by nlinarith
  unfold wbCost
  rw [sq_eq]
  omega

section Cost
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)

/-- The time's coefficient (on `l`, through `J`, `T`, `N`). -/
def bKc (J : ℕ) : ℕ := 10000000 * (J + N.Dn + 2) + T.Cc + N.Cc

/-- **Phase (b)'s time** at the virtual capacity `c`. -/
theorem b_cost_le (J c vN vM vE vT n a nc wl cr fe kh feL t sp L tv ncar capT V : ℕ)
    (hv : vN + vM + vE + vT + V ≤ 5 * c) (hn : n ≤ c) (ha : a ≤ 4) (hnc2 : nc ≤ 2) (hw : wl ≤ c)
    (h3 : (fe + 4) * (n + 3) + 2 * cr + 20 ≤ c) (hk : kh + feL ≤ 2 * c) (hcr : cr ≤ c) (hc1 : 1 ≤ c)
    (ht : t ≤ J * c + J + 1) (hsp : sp ≤ c) (hL : L ≤ c) (htv : tv ≤ c) (hnc : ncar ≤ c) (hcT : capT ≤ c) :
    wa1Cost c vN vM vE vT n a nc wl cr fe kh feL + 1 + wa2Cost c n cr t sp L tv ncar capT N.Dn + 1 +
        (T.cost tv + 1 + N.cost (n + tv + capT)) + 1 + wbCost c vN vM vE vT V ≤
      bKc T N J * (3 * c + 3) ^ ThrDecF.fD T N := by
  have w1 := wa1_le c vN vM vE vT n a nc wl cr fe kh feL (by omega) hn ha hnc2 hw h3 hk
  have w2 := wa2_le c n cr t sp L tv ncar capT N.Dn J hc1 hn hcr ht hsp hL htv hnc hcT
  have w3 := wb_le c vN vM vE vT V hv
  obtain ⟨Bf, hBf⟩ : ∃ B, B = (3 * c + 3) ^ ThrDecF.fD T N := ⟨_, rfl⟩
  have hB3 : (c + 2) * ((c + 2) * (c + 2)) ≤ Bf := by
    have h1 := ThrDecF.pow_fD_ge T N (3 * c + 2) 3 (by unfold ThrDecF.fD; omega)
    have h2 : (c + 2) * ((c + 2) * (c + 2)) ≤ (3 * c + 2 + 1) ^ 3 := by
      have := Nat.pow_le_pow_left (show c + 2 ≤ 3 * c + 2 + 1 by omega) 3
      have e : (c + 2) ^ 3 = (c + 2) * ((c + 2) * (c + 2)) := by ring
      omega
    rw [hBf]; exact h2.trans h1
  have hQ : (c + 2) * (c + 2) ≤ (c + 2) * ((c + 2) * (c + 2)) := Nat.le_mul_of_pos_left _ (by omega)
  have bT : T.cost tv ≤ T.Cc * Bf := by
    have h := T.cost_poly tv
    unfold ValidatorPolynomialDomination.PolyBounded at h
    have h2 : (tv + 1) ^ T.Dc ≤ (3 * c + 2 + 1) ^ T.Dc := Nat.pow_le_pow_left (by omega) _
    have h3 := ThrDecF.pow_fD_ge T N (3 * c + 2) T.Dc (by unfold ThrDecF.fD; omega)
    rw [hBf]
    exact h.trans (Nat.mul_le_mul_left _ (h2.trans h3))
  have bN : N.cost (n + tv + capT) ≤ N.Cc * Bf := by
    have h := N.cost_poly (n + tv + capT)
    unfold ValidatorPolynomialDomination.PolyBounded at h
    have h2 : (n + tv + capT + 1) ^ N.Dc ≤ (3 * c + 2 + 1) ^ N.Dc := Nat.pow_le_pow_left (by omega) _
    have h3 := ThrDecF.pow_fD_ge T N (3 * c + 2) N.Dc (by unfold ThrDecF.fD; omega)
    rw [hBf]
    exact h.trans (Nat.mul_le_mul_left _ (h2.trans h3))
  have bK : (N.Dn + 2 + 0) * ((c + 2) * ((c + 2) * (c + 2))) ≤ (J + N.Dn + 2) * Bf :=
    Nat.mul_le_mul (by omega) hB3
  have w2' : 1000000 * ((J + N.Dn + 2) * ((c + 2) * ((c + 2) * (c + 2)))) ≤ 1000000 * ((J + N.Dn + 2) * Bf) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hB3)
  have hB1 : Bf ≤ (J + N.Dn + 2) * Bf := Nat.le_mul_of_pos_left _ (by omega)
  have hQB : (c + 2) * (c + 2) ≤ Bf := hQ.trans hB3
  have t1 : wa1Cost c vN vM vE vT n a nc wl cr fe kh feL ≤ 20000 * ((J + N.Dn + 2) * Bf) := by
    have := Nat.mul_le_mul_left 20000 (hQB.trans hB1); omega
  have t2 : wa2Cost c n cr t sp L tv ncar capT N.Dn ≤ 1000000 * ((J + N.Dn + 2) * Bf) := w2.trans w2'
  have t3 : wbCost c vN vM vE vT V ≤ 500000 * ((J + N.Dn + 2) * Bf) := by
    have := Nat.mul_le_mul_left 500000 (hQB.trans hB1); omega
  have t4 : 1 ≤ (J + N.Dn + 2) * Bf := by
    have h1 : 1 ≤ Bf := le_trans (by nlinarith) hQB
    exact le_trans h1 hB1
  have e : bKc T N J * Bf = 10000000 * ((J + N.Dn + 2) * Bf) + T.Cc * Bf + N.Cc * Bf := by unfold bKc; ring
  rw [← hBf, e]
  omega

end Cost

end NearCubicWires.WireExponent3_5.PrimT.NwB
