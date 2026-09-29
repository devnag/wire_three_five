import Proof.Wire_3_5.UnionMachine.ThrDimN

/-! # T-A2, part 3: the stage's steps `c2G` within `K_c·(W+n+1)^{D_c}`, `D_c` fixed by `l`

The stage's steps `2·numsStageCostT2 W P … + 2` (the fill `W`, the reader, phases A–C, the tail) at the capacity
`2W + 2`: every piece is a polynomial in the atoms (`W`, `n`, `c_r`, `t`, `Λ̄`, `B_T·L`, `k'`, `C_D`, `K_f`, `K_L`, `s_p`)
of degree `≤ 6`, and every atom is below `Y_c = 2W + 4 + Y` (`Y = YB`, part 2) at EVERY star parameter:

* `sq_le'`, `stepCost_le'`, `qA_le`, `qB1_le`, `qB_le`, `qC_le`, `tail_le`, `head_le`, **`c2_Y`** (`c2G ≤ K_{c0}·Y_c⁶`);
* `yc_le` (`Y_c ≤ c_c·(W+n+1)^{Z_Y}`), **`DcG`** (`l` only), **`KcG`**, **`c2_leG`** (T-A2's `c2_le`).

Paper quantity of the main type: the THR dimension stage's running time, polynomial in the fill and `n`
(prim:runtime P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Transfer

theorem sq_le' (cap Y : ℕ) (h : cap + 2 ≤ Y) : UnaryPow.sq cap ≤ 200 * Y ^ 2 := by
  unfold UnaryPow.sq
  calc 200 * (cap + 2) * (cap + 2) ≤ 200 * Y * Y := Nat.mul_le_mul (Nat.mul_le_mul_left _ h) h
    _ = 200 * Y ^ 2 := by ring

theorem stepCost_le' (X S Y : ℕ) (hS : S ≤ X + 1) (hX : X + 2 ≤ Y) : LevelW.stepCost X S ≤ 200 * Y ^ 2 := by
  unfold LevelW.stepCost
  have h1 : S * S ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have h2 : S * (18 * S + 8) = 18 * (S * S) + 8 * S := by ring
  have h3 : Y ≤ Y * Y := Nat.le_mul_of_pos_left _ (by omega)
  have e : Y ^ 2 = Y * Y := pow_two Y
  rw [h2, e]
  omega

theorem pw_chain (Y : ℕ) (hY : 1 ≤ Y) : Y ≤ Y ^ 2 ∧ Y ^ 2 ≤ Y ^ 3 ∧ Y ^ 3 ≤ Y ^ 6 := by
  refine ⟨?_, Nat.pow_le_pow_right hY (by norm_num), Nat.pow_le_pow_right hY (by norm_num)⟩
  calc Y = Y ^ 1 := (pow_one _).symm
    _ ≤ Y ^ 2 := Nat.pow_le_pow_right hY (by norm_num)

theorem starCost_le (n cr Y : ℕ) (hn : n + 2 ≤ Y) (hcr : cr ≤ Y) : StarNums.starCost n cr 0 ≤ 430 * Y ^ 2 := by
  unfold StarNums.starCost
  have g1 : (n + 2) * (n + 2) ≤ Y ^ 2 := (Nat.mul_le_mul hn hn).trans_eq (pow_two Y).symm
  have g2 := (pw_chain Y (by omega)).1
  have e1 : 400 * (n + 2) * (n + 2) = 400 * ((n + 2) * (n + 2)) := by ring
  have e2 : 25 * 0 * (n + 2) = 0 := by ring
  rw [e1, e2]
  omega

section Pieces
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)

theorem qA_le (cap Y : ℕ) (P : Shared.StarParams) (cr : ℕ) (hcap : cap + 2 ≤ Y) (hn : P.n + 2 ≤ Y) (hcr : cr ≤ Y)
    (ht : Ledger.rowBt h0 h1 P.n + 5 ≤ Y) (hΛ : Ledger.rowBLambda h0 h1 2 P.n ≤ Y) :
    NumsXT2.qACost cap P h0 h1 Cδ C cr ≤ 1000000 * Y ^ 3 := by
  obtain ⟨p12, p23, -⟩ := pw_chain Y (by omega)
  have hsq := sq_le' cap Y hcap
  have hst := starCost_le P.n cr Y hn hcr
  have g5 : (Ledger.rowBt h0 h1 P.n + 5) * (40 * UnaryPow.sq cap) ≤ 8000 * Y ^ 3 :=
    (Nat.mul_le_mul ht (Nat.mul_le_mul_left 40 hsq)).trans_eq (by ring)
  have g7 : ((cap + 2) * 200 + 1500) * UnaryPow.sq cap ≤ 340000 * Y ^ 3 := by
    have a : (cap + 2) * 200 + 1500 ≤ 1700 * Y := by omega
    exact (Nat.mul_le_mul a hsq).trans_eq (by ring)
  have hk : P.k ≤ P.n := NumsX.rs_le P
  have hs : P.s ≤ P.k := by
    show P.s ≤ P.r * P.s
    exact Nat.le_mul_of_pos_left _ P.r_pos
  have hb : P.b ≤ P.n := (Nat.le_mul_of_pos_left _ P.r_pos).trans P.r_mul_b_le
  have hr : P.r ≤ P.n := by have := P.four_r_le_n; omega
  have hk2 := NumsX.kh2_le P
  have hL : Nat.clog 2 (P.n + 2) ≤ P.n + 2 := clog_le P.n
  have hnrb : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  unfold NumsXT2.qACost
  omega

theorem qB1_le (cap Y : ℕ) (P : Shared.StarParams) (hcap : cap + 2 ≤ Y) (hn : P.n + 2 ≤ Y) :
    NumsXT2.qB1Cost cap P h0 h1 Cδ C ≤ 10000 * Y ^ 2 := by
  have p12 := (pw_chain Y (by omega)).1
  have hsq := sq_le' cap Y hcap
  have hr : P.r ≤ P.n := by have := P.four_r_le_n; omega
  have hm : P.n % P.r ≤ P.n := Nat.mod_le _ _
  have hq : P.n / P.r ≤ P.n := Nat.div_le_self _ _
  have hnb : natBitLength (P.n / P.r + 1) ≤ P.n / P.r + 2 := by
    show Nat.log 2 (P.n / P.r + 1) + 1 ≤ _
    have := Nat.log_le_self 2 (P.n / P.r + 1); omega
  have hL : Nat.clog 2 (P.n + 2) ≤ P.n + 2 := clog_le P.n
  unfold NumsXT2.qB1Cost
  generalize UnaryPow.sq cap = q at hsq ⊢
  generalize natBitLength (P.n / P.r + 1) = nb at hnb ⊢
  generalize P.n % P.r = m at hm ⊢
  generalize P.n / P.r = d at hq hnb ⊢
  generalize Nat.clog 2 (P.n + 2) = L at hL ⊢
  generalize Y ^ 2 = Y2 at p12 hsq ⊢
  ring_nf
  omega

theorem qB_le (cap Y : ℕ) (P : Shared.StarParams) (CD Kf : ℕ) (hcap : cap + 2 ≤ Y) (hn : P.n + 2 ≤ Y)
    (hX : Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * Nat.clog 2 (P.n + 2) + 2 ≤ Y)
    (hkp : P.r * natBitLength (P.n / P.r + 1) + Nat.clog 2 (P.n + 2) ≤ Y) (hCD : CD ≤ Y) (hKf : Kf ≤ Y)
    (hsp : Ledger.rowBSparse h0 h1 2 Cδ P.n ≤ Y) :
    NumsXT2.qBCost cap P h0 h1 Cδ C CD Kf ≤ 100000 * Y ^ 3 := by
  obtain ⟨p12, p23, -⟩ := pw_chain Y (by omega)
  have hsq := sq_le' cap Y hcap
  have hL : Nat.clog 2 (P.n + 2) ≤ P.n + 2 := clog_le P.n
  obtain ⟨X, hXd⟩ : ∃ X, X = Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n *
      Nat.clog 2 (P.n + 2) := ⟨_, rfl⟩
  have hst := stepCost_le' X (CanonicalFourfoldRowProgram.natCeilSqrt X) Y (LevelW.natCeilSqrt_le X) (by omega)
  have hprod : (X + 1) * (LevelW.stepCost X (CanonicalFourfoldRowProgram.natCeilSqrt X) + 4) ≤ 204 * Y ^ 3 := by
    have a : LevelW.stepCost X (CanonicalFourfoldRowProgram.natCeilSqrt X) + 4 ≤ 204 * Y ^ 2 := by omega
    exact (Nat.mul_le_mul (show X + 1 ≤ Y by omega) a).trans_eq (by ring)
  unfold NumsXT2.qBCost
  rw [← hXd]
  generalize (X + 1) * (LevelW.stepCost X (CanonicalFourfoldRowProgram.natCeilSqrt X) + 4) = pv at hprod ⊢
  generalize UnaryPow.sq cap = q at hsq ⊢
  generalize P.r * natBitLength (P.n / P.r + 1) = kp at hkp ⊢
  generalize Ledger.rowBSparse h0 h1 2 Cδ P.n = sp at hsp ⊢
  generalize Nat.clog 2 (P.n + 2) = L at hL hkp ⊢
  generalize Y ^ 2 = Y2 at p12 p23 hsq ⊢
  generalize Y ^ 3 = Y3 at p23 hprod ⊢
  ring_nf
  omega

theorem qC_le (Y : ℕ) (P : Shared.StarParams) (CD Kf : ℕ) (hY : 1 ≤ Y) (hn : P.n + 2 ≤ Y)
    (hB : Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n ≤ Y)
    (hX : Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * Nat.clog 2 (P.n + 2) + 2 ≤ Y)
    (hD : (CanonicalFourfoldRowProgram.natCeilSqrt
      (Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * Nat.clog 2 (P.n + 2)) + 1) +
      Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2) ≤ Y)
    (hkp : P.r * natBitLength (P.n / P.r + 1) + Nat.clog 2 (P.n + 2) ≤ Y) (hCD : CD ≤ Y) (hKf : Kf ≤ Y) :
    NumsXT2.qCCost P h0 h1 Cδ C CD Kf ≤ 30 * Y ^ 6 := by
  obtain ⟨p12, p23, p36⟩ := pw_chain Y hY
  have hr : P.r ≤ P.n := by have := P.four_r_le_n; omega
  have hT := tT_shape (P.r * natBitLength (P.n / P.r + 1)) (Nat.clog 2 (P.n + 2))
    (CanonicalFourfoldRowProgram.natCeilSqrt
      (Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * Nat.clog 2 (P.n + 2))) CD Kf Y
    hY hkp hD hCD hKf
  have hD2 : ((CanonicalFourfoldRowProgram.natCeilSqrt
      (Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * Nat.clog 2 (P.n + 2)) + 1) +
      Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2)) * CD ≤ Y ^ 2 :=
    (Nat.mul_le_mul hD hCD).trans_eq (pow_two Y).symm
  unfold NumsXT2.qCCost
  generalize ((((P.r * natBitLength (P.n / P.r + 1) + Nat.clog 2 (P.n + 2)) *
      (P.r * natBitLength (P.n / P.r + 1) + Nat.clog 2 (P.n + 2))) *
      (((CanonicalFourfoldRowProgram.natCeilSqrt
      (Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * Nat.clog 2 (P.n + 2)) + 1) +
      Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2)) * CD) + P.r * natBitLength (P.n / P.r + 1)) +
      Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2)) * CD * Kf = T at hT ⊢
  generalize ((CanonicalFourfoldRowProgram.natCeilSqrt
      (Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * Nat.clog 2 (P.n + 2)) + 1) +
      Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2)) * CD = D2 at hD2 ⊢
  generalize CanonicalFourfoldRowProgram.natCeilSqrt
      (Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * Nat.clog 2 (P.n + 2)) = S at hD ⊢
  generalize Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2) = LL at hD ⊢
  generalize Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * Nat.clog 2 (P.n + 2) = X at hX ⊢
  generalize Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n = B at hB ⊢
  generalize P.r * natBitLength (P.n / P.r + 1) = kp at hkp ⊢
  generalize Nat.clog 2 (P.n + 2) = L at hkp ⊢
  generalize Y ^ 2 = Y2 at p12 p23 hD2 ⊢
  generalize Y ^ 3 = Y3 at p23 p36 ⊢
  generalize Y ^ 6 = Y6 at p36 hT ⊢
  ring_nf
  omega

theorem tail_le (cap Y : ℕ) (P : Shared.StarParams) (KL cr Tv : ℕ) (hcap : cap + 2 ≤ Y) (hn : P.n + 2 ≤ Y)
    (hcr : cr ≤ Y) (hKL : KL ≤ Y) (hT : Tv ≤ 3 * Y ^ 6) :
    NumsXS.tailCost cap P KL cr Tv ≤ 5000 * Y ^ 6 := by
  obtain ⟨p12, p23, p36⟩ := pw_chain Y (by omega)
  have hsq := sq_le' cap Y hcap
  have hst := starCost_le P.n cr Y hn hcr
  have hK : KL * (P.n + 2) * (P.n + 2) ≤ Y ^ 3 :=
    (Nat.mul_le_mul (Nat.mul_le_mul hKL hn) hn).trans_eq (by ring)
  unfold NumsXS.tailCost
  generalize KL * (P.n + 2) * (P.n + 2) = kv at hK ⊢
  generalize StarNums.starCost P.n cr 0 = sc at hst ⊢
  generalize UnaryPow.sq cap = q at hsq ⊢
  generalize Y ^ 2 = Y2 at p12 p23 hsq hst ⊢
  generalize Y ^ 3 = Y3 at p23 p36 hK ⊢
  generalize Y ^ 6 = Y6 at p36 hT ⊢
  ring_nf
  omega

theorem head_le (Y n : ℕ) (hn : n + 3 ≤ Y) : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 200 * Y ^ 2 := by
  have h1 : natBitLength n + 2 ≤ Y := by
    show Nat.log 2 n + 1 + 2 ≤ Y
    have := Nat.log_le_self 2 n; omega
  have h2 := CopyNat.two_pow_natBitLength_le n
  have h3 : 40 * 2 ^ natBitLength n + 40 ≤ 200 * Y := by omega
  exact (Nat.mul_le_mul h1 h3).trans_eq (by ring)

end Pieces

/-! ## The stage's steps -/

section Cost
variable (l : Literals) (F : GateFree l) (KL Kf : ℕ)

/-- The steps' master bound at the fill `W`. -/
noncomputable def Yc (W n : ℕ) : ℕ := 2 * W + 4 + YB l F KL Kf n

/-- The steps' coefficient in `Y_c⁶`. -/
def Kc0 : ℕ := 4000000

theorem c2_Y (W : ℕ) (P : Shared.StarParams) : ThrDim.c2G l F KL Kf W P ≤ Kc0 * Yc l F KL Kf W P.n ^ 6 := by
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = Yc l F KL Kf W P.n := ⟨_, rfl⟩
  rw [← hYd]
  have hYB : YB l F KL Kf P.n ≤ Y := by rw [hYd]; unfold Yc; omega
  have hY1 : 1 ≤ Y := by rw [hYd]; unfold Yc; omega
  obtain ⟨p12, p23, p36⟩ := pw_chain Y hY1
  have hcap : 2 * W + 2 + 2 ≤ Y := by rw [hYd]; unfold Yc; omega
  have hn : P.n + 2 ≤ Y := (yb_n l F KL Kf P.n).trans hYB
  have hn3 : P.n + 3 ≤ Y := by
    have := yb_n l F KL Kf P.n; rw [hYd]; unfold Yc; omega
  have hcr : F.cr ≤ Y := (yb_cr l F KL Kf P.n).trans hYB
  have hKL : KL ≤ Y := (yb_KL l F KL Kf P.n).trans hYB
  have hCD : F.CD ≤ Y := (yb_CD l F KL Kf P.n).trans hYB
  have hKf : Kf ≤ Y := (yb_Kf l F KL Kf P.n).trans hYB
  have ht : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n + 5 ≤ Y := (yb_t l F KL Kf P.n).trans hYB
  have hΛ : Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 P.n ≤ Y := (yb_lam l F KL Kf P.n).trans hYB
  have hB : ThrDim.bT l P ≤ Y := (yb_B l F KL Kf P).trans hYB
  have hX : ThrDim.bT l P * Nat.clog 2 (P.n + 2) + 2 ≤ Y := (yb_X l F KL Kf P).trans hYB
  have hD := (yb_D l F KL Kf P).trans hYB
  have hkp := (yb_kp l F KL Kf P).trans hYB
  have hsp := (yb_sp l F KL Kf P.n).trans hYB
  have hA := qA_le (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) (2 * W + 2) Y P F.cr hcap hn hcr ht hΛ
  have hB1 := qB1_le (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) (2 * W + 2) Y P hcap hn
  have hBB := qB_le (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) (2 * W + 2) Y P F.CD Kf hcap hn hX hkp
    hCD hKf hsp
  have hC := qC_le (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) Y P F.CD Kf hY1 hn hB hX hD hkp hCD hKf
  have hT := tT_shape (P.r * natBitLength (P.n / P.r + 1)) (Nat.clog 2 (P.n + 2))
    (CanonicalFourfoldRowProgram.natCeilSqrt (ThrDim.bT l P * Nat.clog 2 (P.n + 2))) F.CD Kf Y hY1 hkp hD hCD hKf
  have hTl := tail_le (2 * W + 2) Y P KL F.cr
    (NumsXT2.tT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf) hcap hn hcr hKL hT
  have hH := head_le Y P.n hn3
  have hW : W ≤ Y := by rw [hYd]; unfold Yc; omega
  show 2 * (11 * W + 20 + 1 + 1 + 1 + ((natBitLength P.n + 2) * (40 * 2 ^ natBitLength P.n + 40) + 1 +
    (NumsXT2.qACost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.cr + 1 +
      (NumsXT2.qB1Cost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) + 1 +
        (NumsXT2.qBCost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf + 1 +
          NumsXT2.qCCost P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf)) + 1 +
      NumsXS.tailCost (2 * W + 2) P KL F.cr
        (NumsXT2.tT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf)))) + 2 ≤ _
  unfold Kc0
  generalize NumsXS.tailCost (2 * W + 2) P KL F.cr
    (NumsXT2.tT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf) = a5 at hTl ⊢
  generalize NumsXT2.qCCost P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf = a4 at hC ⊢
  generalize NumsXT2.qBCost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf = a3
    at hBB ⊢
  generalize NumsXT2.qB1Cost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) = a2 at hB1 ⊢
  generalize NumsXT2.qACost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.cr = a1
    at hA ⊢
  generalize (natBitLength P.n + 2) * (40 * 2 ^ natBitLength P.n + 40) = a0 at hH ⊢
  generalize Y ^ 2 = Y2 at p12 p23 hB1 hH ⊢
  generalize Y ^ 3 = Y3 at p23 p36 hA hBB ⊢
  generalize Y ^ 6 = Y6 at p36 hC hTl ⊢
  ring_nf
  omega

/-- The steps' master bound against `W + n + 1`. -/
noncomputable def cc (l : Literals) (F : GateFree l) (KL Kf : ℕ) : ℕ := 6 + cY l F KL Kf * 2 ^ ZY l

theorem yc_le (W n : ℕ) : Yc l F KL Kf W n ≤ cc l F KL Kf * (W + n + 1) ^ ZY l := by
  have hZ : 1 ≤ ZY l := by unfold ZY; omega
  have hV : W + n + 1 ≤ (W + n + 1) ^ ZY l := by
    calc W + n + 1 = (W + n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hZ
  have hN : (n + 2) ^ ZY l ≤ 2 ^ ZY l * (W + n + 1) ^ ZY l := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have hY : YB l F KL Kf n ≤ cY l F KL Kf * 2 ^ ZY l * (W + n + 1) ^ ZY l := by
    unfold YB; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hN
  unfold Yc cc
  have e : (6 + cY l F KL Kf * 2 ^ ZY l) * (W + n + 1) ^ ZY l =
      6 * (W + n + 1) ^ ZY l + cY l F KL Kf * 2 ^ ZY l * (W + n + 1) ^ ZY l := by ring
  rw [e]
  omega

/-- **The steps' exponent** (the literals only). -/
noncomputable def DcG (l : Literals) : ℕ := 6 * ZY l

/-- **The steps' coefficient** (after `F`, `K_L`, `K_f`). -/
noncomputable def KcG : ℕ := Kc0 * cc l F KL Kf ^ 6

/-- **T-A2 `c2_le`**: the stage's steps within `K_c·(W+n+1)^{D_c}`, `D_c = DcG l`. -/
theorem c2_leG (W : ℕ) (P : Shared.StarParams) :
    ThrDim.c2G l F KL Kf W P ≤ KcG l F KL Kf * (W + P.n + 1) ^ DcG l := by
  refine (c2_Y l F KL Kf W P).trans ?_
  have h := Nat.pow_le_pow_left (yc_le l F KL Kf W P.n) 6
  calc Kc0 * Yc l F KL Kf W P.n ^ 6 ≤ Kc0 * (cc l F KL Kf * (W + P.n + 1) ^ ZY l) ^ 6 := Nat.mul_le_mul_left _ h
    _ = KcG l F KL Kf * (W + P.n + 1) ^ DcG l := by unfold KcG DcG; rw [mul_pow, ← pow_mul]; ring

end Cost

end NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
