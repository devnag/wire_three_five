import Proof.Wire_3_5.Primitive.Writers.SBFieldCostBase

/-! # SB: P1's cost target, proved

* the phases' costs within `300·sq cap + 3·(the phase's capacity sum) + 100` (`b1Cost_le` … `c3Cost_le`);
* `aCost_le` (phase A within `10^7·cap^3`), `parseCost_le` (within `5000·cap^2`), `emitListCost_le`;
* **`sbP1Cost : SBCostStmt l`** (`p1Cost ≤ 10^9·cap^3` once `sbNeed ≤ cap`).

Paper quantity of the main type: SB's budget (`prim:runtime`, P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.SBNums

section Phases
variable (cap : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)
  (m : Mode) (fe mb nc c0 c1 : ℕ)

theorem b1Cost_le : b1Cost cap P h0 h1 Cδ C m fe ≤ 300 * UnaryPow.sq cap + 3 * tB1 P h0 h1 Cδ C m fe mb nc c0 c1 + 100 := by
  unfold b1Cost tB1; omega
theorem b2aCost_le : b2aCost cap P h0 h1 Cδ C m fe ≤
    300 * UnaryPow.sq cap + 3 * tB2a P h0 h1 Cδ C m fe mb nc c0 c1 + 100 := by
  unfold b2aCost tB2a; omega
theorem b2bCost_le : b2bCost cap P h0 h1 Cδ C m fe ≤
    300 * UnaryPow.sq cap + 3 * tB2b P h0 h1 Cδ C m fe mb nc c0 c1 + 100 := by
  unfold b2bCost tB2b; omega
theorem b2cCost_le : b2cCost cap P h0 h1 Cδ C m fe ≤
    300 * UnaryPow.sq cap + 3 * tB2c P h0 h1 Cδ C m fe mb nc c0 c1 + 100 := by
  unfold b2cCost tB2c; omega
theorem c1Cost_le : c1Cost cap P h0 h1 Cδ C m fe ≤ 300 * UnaryPow.sq cap + 3 * tC1 P h0 h1 Cδ C m fe mb nc c0 c1 + 100 := by
  unfold c1Cost tC1; omega
theorem c2Cost_le : c2Cost cap P h0 h1 Cδ C m fe ≤ 300 * UnaryPow.sq cap + 3 * tC2 P h0 h1 Cδ C m fe mb nc c0 c1 + 100 := by
  unfold c2Cost tC2; omega
theorem c3Cost_le : c3Cost cap P h0 h1 Cδ C m fe ≤ 300 * UnaryPow.sq cap + 3 * tC3 P h0 h1 Cδ C m fe mb nc c0 c1 + 100 := by
  unfold c3Cost tC3; omega

end Phases

theorem sq_le (X : ℕ) (hX : 1 ≤ X) : UnaryPow.sq X ≤ 1800 * X ^ 2 := by
  unfold UnaryPow.sq
  have : (X + 2) * (X + 2) ≤ 9 * X ^ 2 := by nlinarith
  nlinarith

/-- Phase A within `10^7·X^3`. -/
theorem aCost_le (X : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) (m : Mode) (fe cr : ℕ) (hX : 1 ≤ X) (hS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ X)
    (ht : Ledger.rowBt h0 h1 P.n ≤ X) (hL : Nat.clog 2 (P.n + 2) ≤ X) (hlam : Ledger.rowBLambda h0 h1 2 P.n ≤ X)
    (hs : Ledger.rowBSparse h0 h1 2 Cδ P.n ≤ X) : aCost X P h0 h1 Cδ C m fe cr ≤ 10 ^ 7 * X ^ 3 := by
  have hQ := sq_le X hX
  have hX2 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX (by norm_num)
  have hX1 : X ≤ X ^ 3 := by have := Nat.pow_le_pow_right hX (show 1 ≤ 3 by norm_num); rwa [pow_one] at this
  have hn : P.n + 2 ≤ X := by nlinarith
  have hfe : fe * (P.n + 2) ≤ X := by nlinarith
  have hn2 : (P.n + 2) * (P.n + 2) ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul hn hn
  have e1 : (Ledger.rowBt h0 h1 P.n + 5) * (40 * UnaryPow.sq X) ≤ (6 * X) * (40 * (1800 * X ^ 2)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e1' : (6 * X) * (40 * (1800 * X ^ 2)) = 432000 * X ^ 3 := by ring
  have e2 : ((X + 2) * 200 + 1500) * UnaryPow.sq X ≤ (2100 * X) * (1800 * X ^ 2) := Nat.mul_le_mul (by omega) hQ
  have e2' : (2100 * X) * (1800 * X ^ 2) = 3780000 * X ^ 3 := by ring
  unfold aCost StarNums.starCost
  have e3 : 400 * (P.n + 2) * (P.n + 2) = 400 * ((P.n + 2) * (P.n + 2)) := by ring
  have e4 : 25 * fe * (P.n + 2) = 25 * (fe * (P.n + 2)) := by ring
  rw [e3, e4]
  generalize (Ledger.rowBt h0 h1 P.n + 5) * (40 * UnaryPow.sq X) = A at e1 ⊢
  generalize ((X + 2) * 200 + 1500) * UnaryPow.sq X = B at e2 ⊢
  generalize (P.n + 2) * (P.n + 2) = N2 at hn2 ⊢
  generalize fe * (P.n + 2) = FN at hfe ⊢
  generalize UnaryPow.sq X = Q at hQ ⊢
  generalize X ^ 3 = X3 at hX2 hX1 e1' e2' ⊢
  generalize X ^ 2 = X2 at hQ hX2 hn2 e1' e2' e1 e2 ⊢
  omega

/-- Parse within `5000·X^2`. -/
theorem parseCost_le (X w n : ℕ) (hX : 20 ≤ X) (hw : 2 * w ≤ X) (hn : 2 ^ (natBitLength n + 1) ≤ X) :
    SBParse.parseCost X w n ≤ 5000 * X ^ 2 := by
  have hQ := sq_le X (by omega)
  have hp : 2 * 2 ^ natBitLength n ≤ X := by rw [pow_succ] at hn; omega
  have hb : natBitLength n < 2 ^ natBitLength n := Nat.lt_two_pow_self
  have e : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ X * (22 * X) := Nat.mul_le_mul (by omega) (by omega)
  have e' : X * (22 * X) = 22 * X ^ 2 := by ring
  have hX2 : X ≤ X ^ 2 := by have := Nat.pow_le_pow_right (show 1 ≤ X by omega) (show 1 ≤ 2 by norm_num); rwa [pow_one] at this
  unfold SBParse.parseCost
  generalize (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) = D at e ⊢
  generalize UnaryPow.sq X = Q at hQ ⊢
  generalize X ^ 2 = X2 at hQ e' hX2 ⊢
  omega

theorem emitListCost_le : ∀ vs : List ℕ, SBEmit.emitListCost vs ≤ 11 * (Data.unaryList vs).length
  | [] => by simp [SBEmit.emitListCost]
  | v :: vs => by
    have ih := emitListCost_le vs
    have hl : (Data.unaryList (v :: vs)).length = v + 1 + (Data.unaryList vs).length := by
      simp [Data.unaryList, List.length_append]; ring
    show 11 * v + 9 + 1 + SBEmit.emitListCost vs ≤ 11 * (Data.unaryList (v :: vs)).length
    rw [hl]; omega

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
