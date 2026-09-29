import Proof.Wire_3_5.Primitive.SeedFix.C4BudC

/-! # C4.K item (h), part 4: the rest of the SYM stage's steps at rate `3/8` (generic)

P3:3098-3100 (the seed-fixing classes), 1200 (the capacity), 3154-3162 (the sample count): the SYM stage's steps
besides the table-rate loop are the front (the request, the unary numbers, the capacity chain at `2^{⌊n/8⌋ + C}`),
the numbers (PA's data stage, the copy-in, the numbers machine at the capacity `2·2^{⌊n/8⌋+C} + 2`, whose steps are
cubic in it: PA's `starCapCost_le`, `reqParseCost_le`, `countsCost_le`), the two modulus searches (`searchCost_le`,
`2^{3ℓ}` with `ℓ = O((B+1)²)`), the sample expansion and the pad. Each is below `K·2^{j⌊n/8⌋}`, `j ≤ 3`.

* `ex_K`, `ex_of`, `capCost2_le`, **`front_ex`**, `symBig_le`, `capB_le`, `symBig_cap_le`, `mid_le`, `mod_le`,
  `samp_le`, **`rest_le`**.

Paper quantity of the main type: the SYM stage's steps outside the table-rate loop, as a rate. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm

/-- A bound `K·2^{j⌊n/8⌋}` is a rate. -/
theorem ex_K {n j K X : ℕ} (h : X ≤ K * 2 ^ (j * (n / 8))) : Ex n j (Nat.clog 2 K) X := by
  unfold Ex
  calc X ≤ K * 2 ^ (j * (n / 8)) := h
    _ ≤ 2 ^ Nat.clog 2 K * 2 ^ (j * (n / 8)) := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by norm_num) K)
    _ = 2 ^ (j * (n / 8) + Nat.clog 2 K) := by rw [← pow_add, add_comm]

theorem ex_of {n j c X : ℕ} (h : Ex n j c X) : X ≤ 2 ^ c * 2 ^ (j * (n / 8)) := by
  unfold Ex at h; rw [← pow_add, add_comm]; exact h

/-- The capacity chain v2 is at rate `1`. -/
theorem capCost2_le (Cc n : ℕ) : C4Cap.capCost2 Cc n ≤ (8 * Cc + 300) * 2 ^ Cc * 2 ^ (n / 8) := by
  obtain ⟨T, hT⟩ : ∃ T, T = 2 ^ C4Cap.capExp2 Cc n := ⟨_, rfl⟩
  have hTe : T = 2 ^ Cc * 2 ^ (n / 8) := by rw [hT]; unfold C4Cap.capExp2; rw [pow_add, mul_comm]
  have hm : C4Cap.capExp2 Cc n ≤ T := hT ▸ Nat.lt_two_pow_self.le
  have hn8 : n / 8 ≤ T := by
    rw [hT]; exact le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by norm_num) (by unfold C4Cap.capExp2; omega))
  have hT1 : 1 ≤ T := hT ▸ Nat.one_le_two_pow
  have hcT : Cc ≤ Cc * T := Nat.le_mul_of_pos_right _ hT1
  have hts : C4Cap.tsCost (C4Cap.capExp2 Cc n) ≤ 16 * C4Cap.capExp2 Cc n + 20 := by unfold C4Cap.tsCost; omega
  have hsrc : srcCost (C4Cap.capExp2 Cc n) = 16 * T + 40 * C4Cap.capExp2 Cc n + 76 := by unfold srcCost; rw [← hT]; ring
  have e : (8 * Cc + 300) * 2 ^ Cc * 2 ^ (n / 8) = 8 * (Cc * T) + 300 * T := by rw [mul_assoc, ← hTe]; ring
  rw [e]
  unfold C4Cap.capCost2 C4Cap.divCost
  omega

/-- **The front's steps are at rate `1`** (generic in the layout's degree `D` and the request's envelope). -/
theorem front_ex (D CL Cd Cc Cw Dw : ℕ) : ∃ c : ℕ, ∀ (L : Lay), L.D = D → ∀ (n : ℕ) (w : List Bool),
    w.length ≤ Cw * (n + 1) ^ Dw → Ex n 1 c (C4Cap.frontCost3 L w n CL Cd Cc) := by
  obtain ⟨c0, hc0⟩ := ex_poly (D + 1 + Dw)
  refine ⟨Nat.clog 2 ((4 * Cw + 110 + RepairOrdinary.PCPSerializerCapacity.coefficient D CL +
    RepairOrdinary.PCPSerializerCapacity.coefficient D Cd) * 2 ^ c0 + (8 * Cc + 300) * 2 ^ Cc), fun L hD n w hw => ex_K ?_⟩
  rw [one_mul]
  have hP := ex_of (hc0 n)
  rw [one_mul] at hP
  obtain ⟨Pn, hPn⟩ : ∃ x, x = (n + 1) ^ (D + 1 + Dw) := ⟨_, rfl⟩
  rw [← hPn] at hP
  have p1 : (n + 1) ^ Dw ≤ Pn := hPn ▸ Nat.pow_le_pow_right (by omega) (by omega)
  have p2 : (n + 1) ^ (D + 1) ≤ Pn := hPn ▸ Nat.pow_le_pow_right (by omega) (by omega)
  have p3 : n + 1 ≤ Pn := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ Pn := hPn ▸ Nat.pow_le_pow_right (by omega) (by omega)
  have hb := PrimAsm.CopyNat.natBitLength_le_self_succ n
  have pw1 := RepairOrdinary.PCPPNativeResourceCost.power_budget D CL n
  have pw2 := RepairOrdinary.PCPPNativeResourceCost.power_budget D Cd n
  have hcap := capCost2_le Cc n
  obtain ⟨X, hX⟩ : ∃ x, x = 2 ^ (n / 8) := ⟨_, rfl⟩
  rw [← hX] at hP hcap
  have q1 : Cw * (n + 1) ^ Dw ≤ Cw * Pn := Nat.mul_le_mul_left _ p1
  have q2 : RepairOrdinary.PCPSerializerCapacity.coefficient D CL * (n + 1) ^ (D + 1) ≤ RepairOrdinary.PCPSerializerCapacity.coefficient D CL * Pn :=
    Nat.mul_le_mul_left _ p2
  have q3 : RepairOrdinary.PCPSerializerCapacity.coefficient D Cd * (n + 1) ^ (D + 1) ≤ RepairOrdinary.PCPSerializerCapacity.coefficient D Cd * Pn :=
    Nat.mul_le_mul_left _ p2
  have hsum : C4Cap.frontCost3 L w n CL Cd Cc ≤ (4 * Cw + 110 + RepairOrdinary.PCPSerializerCapacity.coefficient D CL +
      RepairOrdinary.PCPSerializerCapacity.coefficient D Cd) * Pn + (8 * Cc + 300) * 2 ^ Cc * X := by
    unfold C4Cap.frontCost3 crCost
    rw [hD]
    have e : (4 * Cw + 110 + RepairOrdinary.PCPSerializerCapacity.coefficient D CL + RepairOrdinary.PCPSerializerCapacity.coefficient D Cd) * Pn =
        4 * (Cw * Pn) + 110 * Pn + RepairOrdinary.PCPSerializerCapacity.coefficient D CL * Pn +
          RepairOrdinary.PCPSerializerCapacity.coefficient D Cd * Pn := by ring
    rw [e]
    omega
  calc C4Cap.frontCost3 L w n CL Cd Cc ≤ _ := hsum
    _ ≤ (4 * Cw + 110 + RepairOrdinary.PCPSerializerCapacity.coefficient D CL + RepairOrdinary.PCPSerializerCapacity.coefficient D Cd) *
          (2 ^ c0 * X) + (8 * Cc + 300) * 2 ^ Cc * X := Nat.add_le_add_right (Nat.mul_le_mul_left _ hP) _
    _ = _ := by rw [hX]; ring

/-- **The SYM numbers machine's steps are cubic in its capacity** (PA's `starCapCost_le`, `reqParseCost_le`,
`countsCost_le`), plus the free program's. -/
theorem symBig_le (cap n cr fe t sp L a nc Kb Cmax M fc : ℕ) (hn : n + 2 ≤ cap) (ha : a ≤ 4) (hnc : nc ≤ 4)
    (hKb : Kb ≤ cap) (hC : Cmax ≤ cap) (hM : M ≤ cap) (hcr : cr ≤ cap) (hfe : fe ≤ cap) (ht : t ≤ cap)
    (hsp : sp ≤ cap) (hL : L ≤ cap) :
    C4SymN.symBigCost cap n cr fe t sp L a nc Kb Cmax M fc ≤ 3000000 * ((cap + 2) * (cap + 2) * (cap + 2)) + fc := by
  have r1 := SymSizes.reqParseCost_le n a nc Kb cap (by omega) ha hnc hKb
  have r2 := SymSizes.countsCost_le nc Cmax M cap hnc hC hM
  have r3 := SymSizes.starCapCost_le n cr fe t sp L cap hn hcr hfe ht hsp hL
  obtain ⟨c, hc⟩ : ∃ x, x = cap + 2 := ⟨_, rfl⟩
  rw [← hc] at r1 r2 r3 ⊢
  have hsq : UnaryPow.sq cap = 200 * (c * c) := by unfold UnaryPow.sq; rw [hc]; ring
  have hc2 : 2 ≤ c := by omega
  have g1 : c ≤ c * c := Nat.le_mul_of_pos_left _ (by omega)
  have g2 : c * c ≤ c * c * c := Nat.le_mul_of_pos_right _ (by omega)
  unfold C4SymN.symBigCost numsSCost
  rw [hsq]
  omega

/-- The capacity `2·2^{⌊n/8⌋ + C} + 2`, plus two, is at rate `1`. -/
theorem capB_le (Cc n : ℕ) : 2 * 2 ^ C4Cap.capExp2 Cc n + 2 + 2 ≤ 6 * 2 ^ Cc * 2 ^ (n / 8) := by
  have e : 2 ^ C4Cap.capExp2 Cc n = 2 ^ Cc * 2 ^ (n / 8) := by unfold C4Cap.capExp2; rw [pow_add, mul_comm]
  have h1 : 1 ≤ 2 ^ Cc * 2 ^ (n / 8) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [e, mul_assoc]
  omega

/-- **The SYM numbers machine's steps at the capacity v2 are at rate `3`**, with a free program quadratic in its
capacity. -/
theorem symBig_cap_le (Cc n Kc fc c : ℕ) (hc : c ≤ 3000000 * ((2 * 2 ^ C4Cap.capExp2 Cc n + 2 + 2) *
      (2 * 2 ^ C4Cap.capExp2 Cc n + 2 + 2) * (2 * 2 ^ C4Cap.capExp2 Cc n + 2 + 2)) + fc)
    (hfc : fc ≤ Kc * (2 * 2 ^ C4Cap.capExp2 Cc n + 2 + 1) ^ 2) :
    c ≤ (648000000 + 36 * Kc) * 2 ^ (3 * Cc) * 2 ^ (3 * (n / 8)) := by
  have hB := capB_le Cc n
  obtain ⟨Y, hY⟩ : ∃ x, x = 2 ^ Cc * 2 ^ (n / 8) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ x, x = 2 * 2 ^ C4Cap.capExp2 Cc n + 2 + 2 := ⟨_, rfl⟩
  rw [← hBd] at hc hB
  have hB1 : 2 * 2 ^ C4Cap.capExp2 Cc n + 2 + 1 ≤ B := by omega
  rw [mul_assoc, ← hY] at hB
  have hY3 : 2 ^ (3 * Cc) * 2 ^ (3 * (n / 8)) = Y * Y * Y := by rw [hY]; ring
  have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have c3 : B * B * B ≤ 6 * Y * (6 * Y) * (6 * Y) := Nat.mul_le_mul (Nat.mul_le_mul hB hB) hB
  have c2 : (2 * 2 ^ C4Cap.capExp2 Cc n + 2 + 1) ^ 2 ≤ 6 * Y * (6 * Y) := by
    rw [sq]; exact Nat.mul_le_mul (hB1.trans hB) (hB1.trans hB)
  have g : Y * Y ≤ Y * Y * Y := Nat.le_mul_of_pos_right _ hY1
  have k2 : Kc * (2 * 2 ^ C4Cap.capExp2 Cc n + 2 + 1) ^ 2 ≤ 36 * (Kc * (Y * Y * Y)) := by
    calc Kc * (2 * 2 ^ C4Cap.capExp2 Cc n + 2 + 1) ^ 2 ≤ Kc * (6 * Y * (6 * Y)) := Nat.mul_le_mul_left _ c2
      _ = 36 * (Kc * (Y * Y)) := by ring
      _ ≤ 36 * (Kc * (Y * Y * Y)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ g)
  have e1 : 6 * Y * (6 * Y) * (6 * Y) = 216 * (Y * Y * Y) := by ring
  have e2 : (648000000 + 36 * Kc) * 2 ^ (3 * Cc) * 2 ^ (3 * (n / 8)) = 648000000 * (Y * Y * Y) + 36 * (Kc * (Y * Y * Y)) := by
    rw [mul_assoc, hY3]; ring
  rw [e2]
  omega

/-- The numbers' steps (the data stage, the copy-in, the numbers machine at the unary word `W`). -/
theorem mid_le (cD : ℕ) (u : List Bool) (W c : ℕ) : Lay.midCost cD u W c ≤ cD + 34 * u.length + 22 * W + 2 * c + 100 := by
  unfold Lay.midCost cpZCost bigCost CellLoopD.cpCost
  omega

/-- The two modulus searches and the loop's linear part: `2^{3ℓ}` (S5's `searchCost_le`). -/
theorem mod_le (ell : ℕ) : 2 * Modulus.modCost ell + 80 * ell ≤ 600 * 2 ^ (3 * ell) := by
  have hs := GF2.searchCost_le ell (ell + 1) (by omega) (by omega)
  have h1 : ell + 1 ≤ 2 ^ ell := Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * ell) * (ell + 1) ^ 1 ≤ 2 ^ (3 * ell) := by
    rw [pow_one]
    calc 2 ^ (2 * ell) * (ell + 1) ≤ 2 ^ (2 * ell) * 2 ^ ell := Nat.mul_le_mul_left _ h1
      _ = 2 ^ (3 * ell) := by rw [← pow_add]; ring_nf
  have h3 : 2 ^ ell ≤ 2 ^ (3 * ell) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold Modulus.modCost
  omega

/-- The sample expansion's steps: `2^{20}(Q+1)(ℓ+1)⁴ ≤ 2^{20}(Q+1)2^{4ℓ}`. -/
theorem samp_le (P : Sampler.SeedParams) : C4Iface.sampCost P ≤ 1048576 * (P.Q + 1) * 2 ^ (4 * P.ell) := by
  unfold C4Iface.sampCost
  have h1 : P.ell + 1 ≤ 2 ^ P.ell := Nat.lt_two_pow_self
  have h2 : (P.ell + 1) ^ 4 ≤ 2 ^ (4 * P.ell) := by
    calc (P.ell + 1) ^ 4 ≤ (2 ^ P.ell) ^ 4 := Nat.pow_le_pow_left h1 4
      _ = 2 ^ (4 * P.ell) := by rw [← pow_mul, mul_comm]
  exact Nat.mul_le_mul_left _ h2

/-- **The rest of the SYM stage's steps at rate `3`** (hence below the table class, `ex_final`): the front, the
numbers, the modulus searches, the loop's linear part, the sample expansion and the pad, each below `K·2^{j⌊n/8⌋}`. -/
theorem rest_le (L : Lay) (w : List Bool) (n CL Cd Cc cD : ℕ) (u : List Bool) (c ell d2 ρ samp P : ℕ)
    (KF KD KU KC Kl K2 KR KS KP : ℕ)
    (hF : C4Cap.frontCost3 L w n CL Cd Cc ≤ KF * 2 ^ (n / 8)) (hD : cD ≤ KD * 2 ^ (n / 8))
    (hU : u.length ≤ KU * 2 ^ (n / 8)) (hc : c ≤ KC * 2 ^ (3 * (n / 8))) (hl : 2 ^ (3 * ell) ≤ Kl * 2 ^ (n / 8))
    (hd2 : d2 ≤ K2 * 2 ^ (n / 8)) (hρ : ρ ≤ KR * 2 ^ (n / 8)) (hs : samp ≤ KS * 2 ^ (n / 8))
    (hP : P ≤ KP * 2 ^ (n / 8)) :
    Ex n 7 (Nat.clog 2 (KF + KD + 34 * KU + 22 * 2 ^ Cc + 2 * KC + 600 * Kl + 40 * K2 + 40 * KR + KS + KP + 400))
      (C4Cap.frontCost3 L w n CL Cd Cc + Lay.midCost cD u (2 ^ C4Cap.capExp2 Cc n) c +
        2 * Modulus.modCost ell + 40 * (d2 + ρ) + 80 * ell + samp + P + 300) := by
  refine ex_mono (j := 3) (by norm_num) le_rfl (ex_K ?_)
  have hm := mid_le cD u (2 ^ C4Cap.capExp2 Cc n) c
  have hmod := mod_le ell
  obtain ⟨X, hX⟩ : ∃ x, x = 2 ^ (n / 8) := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := hX ▸ Nat.one_le_two_pow
  have hX3 : 2 ^ (3 * (n / 8)) = X * X * X := by rw [hX]; ring
  have hW : 2 ^ C4Cap.capExp2 Cc n = 2 ^ Cc * X := by rw [hX]; unfold C4Cap.capExp2; rw [pow_add, mul_comm]
  rw [← hX] at hF hD hU hl hd2 hρ hs hP
  rw [hX3] at hc ⊢
  have g1 : X ≤ X * X * X := by
    calc X = X * 1 * 1 := by ring
      _ ≤ X * X * X := Nat.mul_le_mul (Nat.mul_le_mul_left _ hX1) hX1
  have g0 : 1 ≤ X * X * X := hX1.trans g1
  have m1 : ∀ K : ℕ, K * X ≤ K * (X * X * X) := fun K => Nat.mul_le_mul_left _ g1
  have hl' : 2 ^ (3 * ell) ≤ Kl * (X * X * X) := hl.trans (m1 Kl)
  have hell : ell ≤ 2 ^ (3 * ell) := le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have t1 := m1 KF
  have t2 := m1 KD
  have t3 := m1 KU
  have t4 : 2 ^ C4Cap.capExp2 Cc n ≤ 2 ^ Cc * (X * X * X) := by rw [hW]; exact m1 _
  have t5 := m1 K2
  have t6 := m1 KR
  have t7 := m1 KS
  have t8 := m1 KP
  have e : (KF + KD + 34 * KU + 22 * 2 ^ Cc + 2 * KC + 600 * Kl + 40 * K2 + 40 * KR + KS + KP + 400) * (X * X * X) =
      KF * (X * X * X) + KD * (X * X * X) + 34 * (KU * (X * X * X)) + 22 * (2 ^ Cc * (X * X * X)) +
        2 * (KC * (X * X * X)) + 600 * (Kl * (X * X * X)) + 40 * (K2 * (X * X * X)) + 40 * (KR * (X * X * X)) +
        KS * (X * X * X) + KP * (X * X * X) + 400 * (X * X * X) := by ring
  rw [e]
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4Bud
