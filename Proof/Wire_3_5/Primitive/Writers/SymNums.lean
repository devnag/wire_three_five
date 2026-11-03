import Proof.Wire_3_5.Primitive.Writers.SymNeedBase

/-! # SYM leaf, part 7: the SYM dimension stage's cost, polynomially

The SYM dimension stage (`NumsXS.numsWS`, run within `numsStageCostS W …` at the fill `W`) computes the star numbers,
the sparse count, the SYM cap `B_S`, `S = ⌈√(2^{25}B_S)⌉`, the POP term `T` and the tail. Its cost is at most
`2·10⁹(W+2)³ + 300(X+2)³ + 70·T + 60·K_F(n+2)² + 3(L·D₂ + K₀) + 3D₂ + 10⁹` (`X = 2^{25}B_S`) once the fill `W`
exceeds the small values (`n+2`, `r`, `s`, `b`, `k`, `t+5`, `Λ̄`, `c_r`, the sparse count `s_p`, `L`):

* `stepCost_le`, `pACost_le`, `pBCost_le`, `pCCost_le`, **`numsStageCostS_le`**.

Paper quantity of the main type: the SYM writer's dimension stage cost (prim:runtime P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm.NumsXS

theorem stepCost_le (X S : ℕ) (hS : S ≤ X + 1) : LevelW.stepCost X S ≤ 200 * ((X + 2) * (X + 2)) := by
  unfold LevelW.stepCost
  have h1 : S * S ≤ (X + 2) * (X + 2) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : S * (18 * S + 8) = 18 * (S * S) + 8 * S := by ring
  have h3 : X + 2 ≤ (X + 2) * (X + 2) := Nat.le_mul_of_pos_left _ (by omega)
  rw [h2]
  omega

section
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)

theorem pACost_le (cap : ℕ) (P : Shared.StarParams) (cr : ℕ) (hn : P.n + 2 ≤ cap) (hcr : cr ≤ cap)
    (hs : P.s ≤ cap) (hb : P.b ≤ cap) (hr : P.r ≤ cap) (hk : P.k ≤ cap)
    (ht : Ledger.rowBt h0 h1 P.n + 5 ≤ cap) (hL : Nat.clog 2 (P.n + 2) ≤ cap)
    (hΛ : Ledger.rowBLambda h0 h1 2 P.n ≤ cap) :
    pACost cap P cr h0 h1 Cδ C ≤ 1000000 * ((cap + 2) * (cap + 2) * (cap + 2)) := by
  obtain ⟨c2, hc2⟩ : ∃ x, x = (cap + 2) * (cap + 2) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ x, x = (cap + 2) * (cap + 2) * (cap + 2) := ⟨_, rfl⟩
  have hsq : UnaryPow.sq cap = 200 * c2 := by unfold UnaryPow.sq; rw [hc2]; ring
  have hcc : cap + 2 ≤ c2 := by rw [hc2]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hc23 : c2 ≤ c3 := by rw [hc3, hc2]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hst : StarNums.starCost P.n cr 0 ≤ 430 * c2 := by
    unfold StarNums.starCost
    have g1 : (P.n + 2) * (P.n + 2) ≤ c2 := by rw [hc2]; exact Nat.mul_le_mul (by omega) (by omega)
    have e1 : 400 * (P.n + 2) * (P.n + 2) = 400 * ((P.n + 2) * (P.n + 2)) := by ring
    have e2 : 25 * 0 * (P.n + 2) = 0 := by ring
    rw [e1, e2]; omega
  have hsr : P.s * (P.r / 2) ≤ P.k := by
    show P.s * (P.r / 2) ≤ P.r * P.s
    have := Nat.div_le_self P.r 2
    calc P.s * (P.r / 2) ≤ P.s * P.r := Nat.mul_le_mul_left _ this
      _ = P.r * P.s := by ring
  have g5 : (Ledger.rowBt h0 h1 P.n + 5) * (40 * UnaryPow.sq cap) ≤ 8000 * c3 := by
    rw [hsq]
    have : (Ledger.rowBt h0 h1 P.n + 5) * (40 * (200 * c2)) ≤ (cap + 2) * (8000 * c2) := by
      have e : (Ledger.rowBt h0 h1 P.n + 5) * (40 * (200 * c2)) = (Ledger.rowBt h0 h1 P.n + 5) * (8000 * c2) := by ring
      rw [e]; exact Nat.mul_le_mul_right _ (by omega)
    have e3 : (cap + 2) * (8000 * c2) = 8000 * c3 := by rw [hc3, hc2]; ring
    omega
  have g7 : ((cap + 2) * 200 + 1500) * UnaryPow.sq cap ≤ 340000 * c3 := by
    rw [hsq]
    have e : ((cap + 2) * 200 + 1500) * (200 * c2) = 40000 * ((cap + 2) * c2) + 300000 * c2 := by ring
    have e3 : (cap + 2) * c2 = c3 := by rw [hc3, hc2]; ring
    omega
  have hnrb : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  unfold pACost
  rw [← hc3]
  have hsq2 : UnaryPow.sq cap ≤ 200 * c3 := by rw [hsq]; omega
  omega

theorem pBCost_le (cap : ℕ) (P : Shared.StarParams) (D2 K0 : ℕ) :
    pBCost cap P h0 h1 Cδ C D2 K0 ≤ 40 * UnaryPow.sq cap +
      300 * ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 33554432 + 2) *
        (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 33554432 + 2) *
        (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 33554432 + 2)) +
      3 * Ledger.rowBSparse h0 h1 2 Cδ P.n + 100 := by
  unfold pBCost
  generalize Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n = B
  generalize Ledger.rowBSparse h0 h1 2 Cδ P.n = sp
  generalize UnaryPow.sq cap = q
  obtain ⟨X, hX⟩ : ∃ x, x = B * 33554432 := ⟨_, rfl⟩
  rw [← hX]
  have hS := LevelW.natCeilSqrt_le X
  have hst := stepCost_le X (CanonicalFourfoldRowProgram.natCeilSqrt X) hS
  have hprod : (X + 1) * (LevelW.stepCost X (CanonicalFourfoldRowProgram.natCeilSqrt X) + 4) ≤
      (X + 2) * (200 * ((X + 2) * (X + 2)) + 4) := Nat.mul_le_mul (by omega) (by omega)
  have e : (X + 2) * (200 * ((X + 2) * (X + 2)) + 4) = 200 * ((X + 2) * (X + 2) * (X + 2)) + 4 * (X + 2) := by ring
  have h3 : X + 2 ≤ (X + 2) * (X + 2) * (X + 2) := by
    have a : 1 ≤ (X + 2) * (X + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc X + 2 = (X + 2) * 1 := (mul_one _).symm
      _ ≤ (X + 2) * ((X + 2) * (X + 2)) := Nat.mul_le_mul_left _ a
      _ = _ := by ring
  generalize LevelW.stepCost X (CanonicalFourfoldRowProgram.natCeilSqrt X) = sc at hst hprod ⊢
  linarith

theorem pCCost_le (P : Shared.StarParams) (D2 K0 : ℕ) :
    pCCost P h0 h1 Cδ C D2 K0 ≤
      3 * tSOf (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) D2 K0 (Nat.clog 2 (P.n + 2)) +
      3 * (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 33554432) +
      15 * CanonicalFourfoldRowProgram.natCeilSqrt
        (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 33554432) +
      3 * (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 8192) +
      3 * Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n +
      3 * (Nat.clog 2 (P.n + 2) * D2 + K0) + 3 * D2 + 3 * P.r + 3 * Nat.clog 2 (P.n + 2) + 200000000 := by
  unfold pCCost tSOf
  generalize Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n = B
  linarith

theorem tailCost_eq (cap : ℕ) (P : Shared.StarParams) (KF cr Tv : ℕ) :
    tailCost cap P KF cr Tv = StarNums.starCost P.n cr 0 + 300 * P.n + 600 + 60 * (KF * (P.n + 2) * (P.n + 2)) +
      60 * Tv + 10 * UnaryPow.sq cap + 100 := rfl

/-- **The SYM dimension stage's cost** at the fill `W`. -/
theorem numsStageCostS_le (W : ℕ) (P : Shared.StarParams) (D2 K0 KF cr : ℕ) (hn : P.n + 2 ≤ 2 * W + 2)
    (hcr : cr ≤ 2 * W + 2) (hs : P.s ≤ 2 * W + 2) (hb : P.b ≤ 2 * W + 2) (hr : P.r ≤ 2 * W + 2)
    (hk : P.k ≤ 2 * W + 2) (ht : Ledger.rowBt h0 h1 P.n + 5 ≤ 2 * W + 2) (hL : Nat.clog 2 (P.n + 2) ≤ 2 * W + 2)
    (hΛ : Ledger.rowBLambda h0 h1 2 P.n ≤ 2 * W + 2) :
    numsStageCostS W P h0 h1 Cδ C D2 K0 KF cr ≤
      4000000 * ((2 * W + 4) * (2 * W + 4) * (2 * W + 4)) +
      300 * ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 33554432 + 2) *
        (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 33554432 + 2) *
        (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 33554432 + 2)) +
      63 * tSOf (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) D2 K0 (Nat.clog 2 (P.n + 2)) +
      60 * (KF * (P.n + 2) * (P.n + 2)) +
      15 * CanonicalFourfoldRowProgram.natCeilSqrt
        (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 33554432) +
      6 * (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 33554432) +
      3 * (Nat.clog 2 (P.n + 2) * D2 + K0) + 3 * D2 + 3 * Ledger.rowBSparse h0 h1 2 Cδ P.n + 300000000 := by
  have hA := pACost_le h0 h1 Cδ C (2 * W + 2) P cr hn hcr hs hb hr hk ht hL hΛ
  have hB := pBCost_le h0 h1 Cδ C (2 * W + 2) P D2 K0
  have hC := pCCost_le h0 h1 Cδ C P D2 K0
  have hT : tS P h0 h1 Cδ C D2 K0 =
      tSOf (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) D2 K0 (Nat.clog 2 (P.n + 2)) := rfl
  have hst : StarNums.starCost P.n cr 0 ≤ 430 * ((2 * W + 4) * (2 * W + 4)) := by
    unfold StarNums.starCost
    have g1 : (P.n + 2) * (P.n + 2) ≤ (2 * W + 4) * (2 * W + 4) := Nat.mul_le_mul (by omega) (by omega)
    have e1 : 400 * (P.n + 2) * (P.n + 2) = 400 * ((P.n + 2) * (P.n + 2)) := by ring
    have e2 : 25 * 0 * (P.n + 2) = 0 := by ring
    have g2 : 2 * W + 4 ≤ (2 * W + 4) * (2 * W + 4) := Nat.le_mul_of_pos_left _ (by omega)
    rw [e1, e2]; omega
  have hsq : UnaryPow.sq (2 * W + 2) = 200 * ((2 * W + 4) * (2 * W + 4)) := by unfold UnaryPow.sq; ring
  have hbn := PrimAsm.CopyNat.natBitLength_le_self_succ P.n
  have hpw := PrimAsm.CopyNat.two_pow_natBitLength_le P.n
  have fB : (natBitLength P.n + 2) * (40 * 2 ^ natBitLength P.n + 40) ≤ 360 * ((2 * W + 4) * (2 * W + 4)) := by
    have := Nat.mul_le_mul (show natBitLength P.n + 2 ≤ 3 * (P.n + 1) by omega)
      (show 40 * 2 ^ natBitLength P.n + 40 ≤ 120 * (P.n + 1) by omega)
    have e : 3 * (P.n + 1) * (120 * (P.n + 1)) = 360 * ((P.n + 1) * (P.n + 1)) := by ring
    have g : (P.n + 1) * (P.n + 1) ≤ (2 * W + 4) * (2 * W + 4) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have g23 : (2 * W + 4) * (2 * W + 4) ≤ (2 * W + 4) * (2 * W + 4) * (2 * W + 4) := Nat.le_mul_of_pos_right _ (by omega)
  have gW : W ≤ (2 * W + 4) * (2 * W + 4) := le_trans (by omega) (Nat.le_mul_of_pos_left (2 * W + 4) (by omega))
  have hA3 : (2 * W + 2 + 2) * (2 * W + 2 + 2) * (2 * W + 2 + 2) = (2 * W + 4) * (2 * W + 4) * (2 * W + 4) := by ring
  rw [hA3] at hA
  unfold numsStageCostS numsCostS
  rw [tailCost_eq, hT] at *
  rw [hsq] at hB ⊢
  linarith

end

end NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
