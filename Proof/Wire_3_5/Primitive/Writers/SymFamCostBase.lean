import Proof.Wire_3_5.Primitive.Writers.SymFamBase

/-! # PA2 (SYM leaf), part 12: the SYM writer's budget in the preprocessing class

* `SB.E1`, `SB.d1`, `SB.K1` (the request side `|w| + n + cc + 2 ≤ K₁Q^{d₁}`), `SB.Ec2`, `SB.Kc2` (the dimension stage
  `c₂ ≤ K_{c2}(n+2)^{E_{c2}}`, **`c2_fam`**), **`SB.Etot`** (the budget's exponent: the producers' and the literals'
  exponents only), `SB.Ktot`, **`SB.cWr`** (the writer's coefficient, after `F`), **`SB.EW`** (`c_ψ = E_tot·c_S`);
* **`sym_fam_cost`**: `costS … ≤ c_W·classBound E_W .preprocessing n k Ψ` for every envelope with `c_ψ ≥ E_tot·c_S`
  (`costS ≤ K_tot·Q^{E_tot}`, then `SymSizes.class_linkS`); `SB.Etot_eq` (the exponent reads the exponents only).

Paper quantity of the main type: the SYM writer's running time within `2^{O(Ψ)}q^{O(1)}` (prim:runtime P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline

/-! ## The budget's class link -/

namespace SB
variable (h : SB)

/-- The shell budget's exponent in the request side and in `Q`. -/
def E1 : ℕ := ShellT.EcT h.D h.D2 h.Dv 1
/-- The request side `|w| + n + cc + 2 ≤ K₁·Q^{d₁}`. -/
def d1 : ℕ := h.Dw + h.D2 * h.Dsy + 1
def K1 : ℕ := h.Cw + 2 + h.Csy * (3 * h.C2 + 1) ^ h.Dsy
/-- The dimension stage's cost `c₂ ≤ K_{c2}·(n+2)^{E_{c2}}`. -/
def Ec2 : ℕ := 3 * h.Dv + 3 * h.Z + 3
def Kc2 : ℕ := 1000000000 * ((2 * h.Cv + 4) ^ 3 + (67108864 * h.capK + 2) ^ 3 + h.KT + h.KF + 1)
/-- **The budget's exponent** (the exponents only: the producers' and the literals'). -/
def Etot : ℕ := h.d1 * h.E1 + h.E1 + h.D + 1 + h.Ec2
def Ktot : ℕ := ShellT.KcT h.D h.Kr h.D2 h.C2 h.Dv h.Cv 0 1 h.KA 0 * h.K1 ^ h.E1 +
  ShellT.KcT h.D h.Kr h.D2 h.C2 h.Dv h.Cv 0 1 h.KA 0 + h.KA * (4 * h.Kr + 10) + 2 * h.Kc2
/-- **The SYM writer's coefficient** (after `F`). -/
def cWr : ℕ := h.Ktot * 2 ^ (SymSizes.cFOf h.Etot h.KF h.Z 26 6 h.capK + h.Etot)
/-- **The SYM writer's envelope** (the exponents only). -/
def EW : Cost.Envelope := ⟨0, 0, 0, 0, 0, 0, 0, h.Etot * SymSizes.cSOf h.Z 26⟩

theorem Etot_pos : 1 ≤ h.Etot := by unfold SB.Etot; omega

/-- **The budget's exponent reads the exponents only.** -/
theorem Etot_eq (h' : SB) (e1 : h.Dw = h'.Dw) (e2 : h.Dnw = h'.Dnw) (e3 : h.Dsy = h'.Dsy) (e4 : h.Dn = h'.Dn)
    (e5 : h.Db = h'.Db) (e6 : h.Qd = h'.Qd) (e7 : h.Qe = h'.Qe) (e8 : h.Df = h'.Df) (e9 : h.Dp = h'.Dp)
    (e10 : h.Z = h'.Z) (e11 : h.Zm = h'.Zm) (e12 : h.Csp = h'.Csp) (e13 : h.J = h'.J) (e14 : h.cX = h'.cX) :
    h.Etot = h'.Etot := by
  simp only [SB.Etot, SB.d1, SB.E1, SB.D, SB.dcap, SB.D2, SB.Dv, SB.sA, SB.Ec2, ShellT.EcT, e1, e2, e3, e4, e5, e6, e7,
    e8, e9, e10, e11, e12, e13, e14]

end SB

/-- The dimension stage's cost bound, arithmetic. -/
theorem c2_arith {W B S T KF q sp Cv Dv capK Z KT Csp stage E : ℕ}
    (hc : stage ≤ 4000000 * ((2 * W + 4) * (2 * W + 4) * (2 * W + 4)) +
      300 * ((B * 33554432 + 2) * (B * 33554432 + 2) * (B * 33554432 + 2)) + 63 * T +
      60 * (KF * (q + 2) * (q + 2)) + 15 * S + 6 * (B * 33554432) + 3 * (Nat.clog 2 (q + 2) * 26 + 6) + 3 * 26 +
      3 * sp + 300000000)
    (hW : W = Cv * (q + 1) ^ Dv) (hB : B ≤ capK * (q + 2) ^ Z) (hS : S ≤ B * 33554432 + 1)
    (hT : T ≤ KT * (q + 2) ^ (Z + 2)) (hsp : sp ≤ (q + 2) ^ (Csp + 3))
    (hE1 : 3 * Dv ≤ E) (hE2 : 3 * Z ≤ E) (hE3 : Z + 2 ≤ E) (hE4 : Csp + 3 ≤ E) (hE5 : 2 ≤ E) :
    2 * stage + 2 ≤ 1000000000 * ((2 * Cv + 4) ^ 3 + (67108864 * capK + 2) ^ 3 + KT + KF + 1) * (q + 2) ^ E := by
  obtain ⟨p, hp⟩ : ∃ x, x = (q + 2) ^ E := ⟨_, rfl⟩
  have pd : ∀ d, d ≤ E → (q + 2) ^ d ≤ p := fun d hd => by rw [hp]; exact Nat.pow_le_pow_right (by omega) hd
  have p1 : 1 ≤ p := le_trans (Nat.one_le_pow _ _ (by omega)) (pd 0 (Nat.zero_le _))
  -- the fill
  have w1 : 2 * W + 4 ≤ (2 * Cv + 4) * (q + 2) ^ Dv := by
    have a1 : (q + 1) ^ Dv ≤ (q + 2) ^ Dv := Nat.pow_le_pow_left (by omega) _
    have a2 : 1 ≤ (q + 2) ^ Dv := Nat.one_le_pow _ _ (by omega)
    have e : (2 * Cv + 4) * (q + 2) ^ Dv = 2 * (Cv * (q + 2) ^ Dv) + 4 * (q + 2) ^ Dv := by ring
    have a3 : Cv * (q + 1) ^ Dv ≤ Cv * (q + 2) ^ Dv := Nat.mul_le_mul_left _ a1
    rw [hW]; omega
  have w3 : (2 * W + 4) * (2 * W + 4) * (2 * W + 4) ≤ (2 * Cv + 4) ^ 3 * p := by
    have a := Nat.mul_le_mul (Nat.mul_le_mul w1 w1) w1
    have e : (2 * Cv + 4) * (q + 2) ^ Dv * ((2 * Cv + 4) * (q + 2) ^ Dv) * ((2 * Cv + 4) * (q + 2) ^ Dv) =
        (2 * Cv + 4) ^ 3 * (q + 2) ^ (3 * Dv) := by rw [pow_mul']; ring
    rw [e] at a
    exact le_trans a (Nat.mul_le_mul_left _ (pd _ hE1))
  -- the cap
  have x1 : B * 33554432 + 2 ≤ (67108864 * capK + 2) * (q + 2) ^ Z := by
    have a2 : 1 ≤ (q + 2) ^ Z := Nat.one_le_pow _ _ (by omega)
    have a3 : B * 33554432 ≤ 33554432 * (capK * (q + 2) ^ Z) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hB
    have e : (67108864 * capK + 2) * (q + 2) ^ Z = 67108864 * (capK * (q + 2) ^ Z) + 2 * (q + 2) ^ Z := by ring
    calc B * 33554432 + 2 ≤ 33554432 * (capK * (q + 2) ^ Z) + 2 * (q + 2) ^ Z :=
          Nat.add_le_add a3 (le_of_eq_of_le (by norm_num : 2 = 2 * 1) (Nat.mul_le_mul_left 2 a2))
      _ ≤ 67108864 * (capK * (q + 2) ^ Z) + 2 * (q + 2) ^ Z :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ (by norm_num)) _
      _ = _ := e.symm
  have x3 : (B * 33554432 + 2) * (B * 33554432 + 2) * (B * 33554432 + 2) ≤ (67108864 * capK + 2) ^ 3 * p := by
    have a := Nat.mul_le_mul (Nat.mul_le_mul x1 x1) x1
    have e : (67108864 * capK + 2) * (q + 2) ^ Z * ((67108864 * capK + 2) * (q + 2) ^ Z) *
        ((67108864 * capK + 2) * (q + 2) ^ Z) = (67108864 * capK + 2) ^ 3 * (q + 2) ^ (3 * Z) := by rw [pow_mul']; ring
    rw [e] at a
    exact le_trans a (Nat.mul_le_mul_left _ (pd _ hE2))
  have x1p : B * 33554432 + 2 ≤ (67108864 * capK + 2) ^ 3 * p := by
    have b1 : 1 ≤ (67108864 * capK + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have b2 : (q + 2) ^ Z ≤ p := pd _ (by omega)
    calc B * 33554432 + 2 ≤ (67108864 * capK + 2) * (q + 2) ^ Z := x1
      _ ≤ (67108864 * capK + 2) * (67108864 * capK + 2) ^ 2 * p :=
          Nat.mul_le_mul (Nat.le_mul_of_pos_right _ b1) b2
      _ = (67108864 * capK + 2) ^ 3 * p := by ring
  have t1 : T ≤ KT * p := le_trans hT (Nat.mul_le_mul_left _ (pd _ hE3))
  have k1 : KF * (q + 2) * (q + 2) ≤ KF * p := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (le_of_eq_of_le (by ring) (pd 2 hE5))
  have s1 : sp ≤ p := le_trans hsp (pd _ hE4)
  have l1 : Nat.clog 2 (q + 2) ≤ p := le_trans (clog_le_self _) (le_of_eq_of_le (pow_one _).symm (pd 1 (by omega)))
  have e : 1000000000 * ((2 * Cv + 4) ^ 3 + (67108864 * capK + 2) ^ 3 + KT + KF + 1) * p =
      1000000000 * ((2 * Cv + 4) ^ 3 * p) + 1000000000 * ((67108864 * capK + 2) ^ 3 * p) + 1000000000 * (KT * p) +
        1000000000 * (KF * p) + 1000000000 * p := by ring
  rw [← hp, e]
  omega

section CostC
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive

end CostC

section Cost2
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive

end Cost2

end NearCubicWires.WireExponent3_5.PrimAsm.SymFam
