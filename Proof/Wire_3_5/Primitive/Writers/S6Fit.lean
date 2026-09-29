import Proof.Wire_3_5.FinalPass.S6Iface
import Proof.Wire_3_5.FinalPass.SymFr3

/-! # S6: the final pass's constants `E₅`, `CD₅`, `c₅` and their `fits`

`S6Target := S6Uni → S6Out` (the S6Iface) from the uniformity bundle and the three request-size bounds (N1–N3 of
the satisfiability check, produced; statements verbatim as sent):

* **`FpInBound`** (N1): `|fpIn r| + 1 ≤ K_in·2^k·(n+1)^{D_in}`; **`SeedCountBound`** (N2): `|E| ≤ K_e·(n+1)^{D_e}`;
  **`PtCountBound`** (N3): `ptCount r ≤ K_p·2^{n−⌊k/4⌋}·(n+1)^{D_q}` (exponents chosen before `F`, coefficients after);
* the ℕ bookkeeping `pow_base_le`, `s5_le`, `out_le`, `pre_into`, `main_into`, and **`fits_arith`** (the whole
  residual at explicit atoms);
* `e5` (the envelope: `cpsi = 2D_g + D_g²`, `Apre = D_e + D_in·D_g + D_in·D_g²`, `Amain = D_q + D_g`), `c5v`,
  **`s6_fits`** (`S6Fits` at `E₅ = e5 …` fixed before `F`, `CD₅ = 1`, `c₅ = c5v …` after `F`) and **`s6Target`**.

The front, table, overhead and out-machine terms land in the preprocessing class `2^{cpsi·Ψ}·n^{Apre}` through `k ≤ Ψ`
(`kL_le_loadPsi` at `C_D ≥ 1 = CD₅`); the point term lands in the main pass `2^{n−k/4}·n^{Amain}`.

Paper quantity of the main type: `c₅`, `E₅` and the final pass's running time within `c₅·finalClasses E₅`
(prim:runtime, P3:3105-3115, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.S6Fit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.Assembly

/-! ## The three request-size bounds (N1–N3) -/

section Sizes
variable (l : Literals)

/-- **N1**: the final pass's input length. -/
def FpInBound : Prop := ∀ fe : ℕ, ∃ Din : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ∃ Kin : ℕ,
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha),
      (fpIn l F kclk coef A a ha r).length + 1 ≤
        Kin * 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf r.1.n) * (r.1.n + 1) ^ Din

/-- **N2**: the number of filter seeds. -/
def SeedCountBound : Prop := ∀ fe : ℕ, ∃ De : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ∃ Ke : ℕ,
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha),
      seedCount l F kclk coef A a ha r ≤ Ke * (r.1.n + 1) ^ De

/-- **N3**: the number of point evaluations, in the main pass's shape. -/
def PtCountBound : Prop := ∀ fe : ℕ, ∃ Dq : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ∃ Kp : ℕ,
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha),
      ptCount l F kclk coef A a ha r ≤
        Kp * 2 ^ (r.1.n - ((gate0 l F).budget kclk coef A a ha).kOf r.1.n / 4) * (r.1.n + 1) ^ Dq

end Sizes

section Choice

/-- N1's exponent. -/
noncomputable def dIn (h : ∀ l, FpInBound l) (l : Literals) (fe : ℕ) : ℕ := Classical.choose (h l fe)
/-- N1's coefficient. -/
noncomputable def kIn (h : ∀ l, FpInBound l) (l : Literals) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (h l F.filterErrDeg) F rfl)
theorem kIn_spec (h : ∀ l, FpInBound l) (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) :
    (fpIn l F kclk coef A a ha r).length + 1 ≤
      kIn h l F * 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf r.1.n) * (r.1.n + 1) ^ dIn h l F.filterErrDeg :=
  Classical.choose_spec (Classical.choose_spec (h l F.filterErrDeg) F rfl) kclk coef A a ha r

/-- N2's exponent. -/
noncomputable def dE (h : ∀ l, SeedCountBound l) (l : Literals) (fe : ℕ) : ℕ := Classical.choose (h l fe)
/-- N2's coefficient. -/
noncomputable def kE (h : ∀ l, SeedCountBound l) (l : Literals) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (h l F.filterErrDeg) F rfl)
theorem kE_spec (h : ∀ l, SeedCountBound l) (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) :
    seedCount l F kclk coef A a ha r ≤ kE h l F * (r.1.n + 1) ^ dE h l F.filterErrDeg :=
  Classical.choose_spec (Classical.choose_spec (h l F.filterErrDeg) F rfl) kclk coef A a ha r

/-- N3's exponent. -/
noncomputable def dQ (h : ∀ l, PtCountBound l) (l : Literals) (fe : ℕ) : ℕ := Classical.choose (h l fe)
/-- N3's coefficient. -/
noncomputable def kP (h : ∀ l, PtCountBound l) (l : Literals) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (h l F.filterErrDeg) F rfl)
theorem kP_spec (h : ∀ l, PtCountBound l) (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) :
    ptCount l F kclk coef A a ha r ≤
      kP h l F * 2 ^ (r.1.n - ((gate0 l F).budget kclk coef A a ha).kOf r.1.n / 4) * (r.1.n + 1) ^ dQ h l F.filterErrDeg :=
  Classical.choose_spec (Classical.choose_spec (h l F.filterErrDeg) F rfl) kclk coef A a ha r

end Choice

/-! ## The bookkeeping -/

section Arith

theorem pow_base_le {I K k ψ N d D Dg : ℕ} (hI : 1 ≤ I) (h : I ≤ K * 2 ^ k * N ^ d) (hk : k ≤ ψ) (hD : D ≤ Dg) :
    I ^ D ≤ K ^ Dg * 2 ^ (Dg * ψ) * N ^ (d * Dg) := by
  calc I ^ D ≤ I ^ Dg := Nat.pow_le_pow_right hI hD
    _ ≤ (K * 2 ^ k * N ^ d) ^ Dg := Nat.pow_le_pow_left h Dg
    _ = K ^ Dg * 2 ^ (k * Dg) * N ^ (d * Dg) := by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ K ^ Dg * 2 ^ (Dg * ψ) * N ^ (d * Dg) := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by norm_num)
        rw [Nat.mul_comm k Dg]
        exact Nat.mul_le_mul_left _ hk

theorem s5_le {C D Cg Dg ψ I Kin k N Din : ℕ} (hC : C ≤ Cg) (hD : D ≤ Dg) (hI1 : 1 ≤ I)
    (hI : I ≤ Kin * 2 ^ k * N ^ Din) (hk : k ≤ ψ) :
    C * 2 ^ (D * ψ) * I ^ D ≤ Cg * Kin ^ Dg * 2 ^ ((2 * Dg) * ψ) * N ^ (Din * Dg) := by
  have h1 : 2 ^ (D * ψ) ≤ 2 ^ (Dg * ψ) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hD)
  have h2 := pow_base_le hI1 hI hk hD
  calc C * 2 ^ (D * ψ) * I ^ D ≤ Cg * 2 ^ (Dg * ψ) * (Kin ^ Dg * 2 ^ (Dg * ψ) * N ^ (Din * Dg)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hC h1) h2
    _ = Cg * Kin ^ Dg * 2 ^ ((2 * Dg) * ψ) * N ^ (Din * Dg) := by
        rw [show (2 * Dg) * ψ = Dg * ψ + Dg * ψ by ring, pow_add]; ring

theorem out_le {OC OD W Cw Dw Cg Dg ψ I Kin k N Din : ℕ} (hOC : OC ≤ Cg) (hOD : OD ≤ Dg) (hCw : Cw ≤ Cg)
    (hDw : Dw ≤ Dg) (hW : W ≤ Cw * I ^ Dw) (hI1 : 1 ≤ I) (hI : I ≤ Kin * 2 ^ k * N ^ Din) (hk : k ≤ ψ) :
    OC * (W + 1) ^ OD ≤ Cg * ((Cg + 1) ^ Dg * Kin ^ (Dg * Dg)) * 2 ^ ((Dg * Dg) * ψ) * N ^ (Din * (Dg * Dg)) := by
  have hIg : 1 ≤ I ^ Dg := Nat.one_le_pow _ _ hI1
  have hIw : I ^ Dw ≤ I ^ Dg := Nat.pow_le_pow_right hI1 hDw
  have hCI : Cw * I ^ Dw ≤ Cg * I ^ Dg := Nat.mul_le_mul hCw hIw
  have hW1 : W + 1 ≤ (Cg + 1) * I ^ Dg := by
    calc W + 1 ≤ Cg * I ^ Dg + I ^ Dg := by omega
      _ = (Cg + 1) * I ^ Dg := by ring
  have hW2 : (W + 1) ^ OD ≤ (W + 1) ^ Dg := Nat.pow_le_pow_right (by omega) hOD
  have hW3 : (W + 1) ^ Dg ≤ ((Cg + 1) * I ^ Dg) ^ Dg := Nat.pow_le_pow_left hW1 Dg
  have hW4 : ((Cg + 1) * I ^ Dg) ^ Dg = (Cg + 1) ^ Dg * I ^ (Dg * Dg) := by rw [mul_pow, ← pow_mul]
  have hI2 : I ^ (Dg * Dg) ≤ Kin ^ (Dg * Dg) * 2 ^ ((Dg * Dg) * ψ) * N ^ (Din * (Dg * Dg)) :=
    pow_base_le hI1 hI hk le_rfl
  have hW5 : (W + 1) ^ OD ≤ (Cg + 1) ^ Dg * I ^ (Dg * Dg) := hW4 ▸ (hW2.trans hW3)
  calc OC * (W + 1) ^ OD ≤ Cg * ((Cg + 1) ^ Dg * (Kin ^ (Dg * Dg) * 2 ^ ((Dg * Dg) * ψ) * N ^ (Din * (Dg * Dg)))) :=
        Nat.mul_le_mul hOC (hW5.trans (Nat.mul_le_mul_left _ hI2))
    _ = Cg * ((Cg + 1) ^ Dg * Kin ^ (Dg * Dg)) * 2 ^ ((Dg * Dg) * ψ) * N ^ (Din * (Dg * Dg)) := by ring

theorem pre_into {x K e a cp Ap ψ n : ℕ} (hn : 1 ≤ n) (h : x ≤ K * 2 ^ (e * ψ) * (n + 1) ^ a) (he : e ≤ cp)
    (ha : a ≤ Ap) : x ≤ K * 2 ^ Ap * (2 ^ (cp * ψ) * n ^ Ap) := by
  have h1 : 2 ^ (e * ψ) ≤ 2 ^ (cp * ψ) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ he)
  have h2 : (n + 1) ^ a ≤ (n + 1) ^ Ap := Nat.pow_le_pow_right (by omega) ha
  have h3 : (n + 1) ^ Ap ≤ (2 * n) ^ Ap := Nat.pow_le_pow_left (by omega) Ap
  calc x ≤ K * 2 ^ (e * ψ) * (n + 1) ^ a := h
    _ ≤ K * 2 ^ (cp * ψ) * (2 * n) ^ Ap := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (h2.trans h3)
    _ = K * 2 ^ Ap * (2 ^ (cp * ψ) * n ^ Ap) := by rw [mul_pow]; ring

theorem main_into {x K m a n : ℕ} (hn : 1 ≤ n) (h : x ≤ K * 2 ^ m * (n + 1) ^ a) :
    x ≤ K * 2 ^ a * (2 ^ m * n ^ a) := by
  have h3 : (n + 1) ^ a ≤ (2 * n) ^ a := Nat.pow_le_pow_left (by omega) a
  calc x ≤ K * 2 ^ m * (n + 1) ^ a := h
    _ ≤ K * 2 ^ m * (2 * n) ^ a := Nat.mul_le_mul_left _ h3
    _ = K * 2 ^ a * (2 ^ m * n ^ a) := by rw [mul_pow]; ring

/-- The preprocessing coefficient. -/
def kPre (Cg Dg Kin Ke : ℕ) : ℕ :=
  Cg * Kin ^ Dg + Ke * (Cg * Kin ^ Dg) + Cg * Kin ^ Dg + Cg * ((Cg + 1) ^ Dg * Kin ^ (Dg * Dg)) + 2

/-- **The final pass's coefficient** `c₅` (after `F`). -/
def c5v (Cg Dg Din De Dq Kin Ke Kp : ℕ) : ℕ :=
  kPre Cg Dg Kin Ke * 2 ^ (De + Din * Dg + Din * (Dg * Dg)) + Kp * Cg * 2 ^ (Dq + Dg)

/-- **The residual at explicit atoms**: the front, the seeds phase's table/point/overhead terms and the out machine
within `c5v·(2^{cpsi·ψ}·n^{Apre} + 2^{n−k/4}·n^{Amain})`. -/
theorem fits_arith {n k ψ I W sE nP Cf Df Ct Dt Co Do Cp Dp OC OD Cw Dw Cg Dg Din De Dq Kin Ke Kp : ℕ}
    (hn : 1 ≤ n) (hk : k ≤ ψ) (hI : I ≤ Kin * 2 ^ k * (n + 1) ^ Din) (hI1 : 1 ≤ I)
    (hE : sE ≤ Ke * (n + 1) ^ De) (hP : nP ≤ Kp * 2 ^ (n - k / 4) * (n + 1) ^ Dq) (hW : W ≤ Cw * I ^ Dw)
    (dDf : Df ≤ Dg) (dDw : Dw ≤ Dg) (dDt : Dt ≤ Dg) (dDp : Dp ≤ Dg) (dDo : Do ≤ Dg) (dOD : OD ≤ Dg)
    (cCf : Cf ≤ Cg) (cCw : Cw ≤ Cg) (cCt : Ct ≤ Cg) (cCp : Cp ≤ Cg) (cCo : Co ≤ Cg) (cOC : OC ≤ Cg) :
    Cf * 2 ^ (Df * ψ) * I ^ Df + 1 + (sE * (Ct * 2 ^ (Dt * ψ) * I ^ Dt) + nP * (Cp * (n + 1) ^ Dp) +
      Co * 2 ^ (Do * ψ) * I ^ Do + 1 + OC * (W + 1) ^ OD) ≤
    c5v Cg Dg Din De Dq Kin Ke Kp * (2 ^ ((2 * Dg + Dg * Dg) * ψ) * n ^ (De + Din * Dg + Din * (Dg * Dg)) +
      2 ^ (n - k / 4) * n ^ (Dq + Dg)) := by
  obtain ⟨Pr, hPr⟩ : ∃ x, x = 2 ^ ((2 * Dg + Dg * Dg) * ψ) * n ^ (De + Din * Dg + Din * (Dg * Dg)) := ⟨_, rfl⟩
  obtain ⟨Mn, hMn⟩ : ∃ x, x = 2 ^ (n - k / 4) * n ^ (Dq + Dg) := ⟨_, rfl⟩
  obtain ⟨Ap, hAp⟩ : ∃ x, x = De + Din * Dg + Din * (Dg * Dg) := ⟨_, rfl⟩
  obtain ⟨K1, hK1⟩ : ∃ x, x = Cg * Kin ^ Dg := ⟨_, rfl⟩
  obtain ⟨K4, hK4⟩ : ∃ x, x = Cg * ((Cg + 1) ^ Dg * Kin ^ (Dg * Dg)) := ⟨_, rfl⟩
  have hcp1 : 2 * Dg ≤ 2 * Dg + Dg * Dg := Nat.le_add_right _ _
  have hcp2 : Dg * Dg ≤ 2 * Dg + Dg * Dg := Nat.le_add_left _ _
  have hPr1 : 1 ≤ 2 ^ Ap * Pr := by
    rw [hPr]
    have := Nat.one_le_two_pow (n := Ap)
    have := Nat.one_le_two_pow (n := (2 * Dg + Dg * Dg) * ψ)
    have := Nat.one_le_pow (De + Din * Dg + Din * (Dg * Dg)) n hn
    calc 1 = 1 * (1 * 1) := by ring
      _ ≤ _ := Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
  -- the front
  have a1 : Cf * 2 ^ (Df * ψ) * I ^ Df ≤ K1 * 2 ^ Ap * Pr := by
    rw [hK1, hAp, hPr]
    exact pre_into hn (s5_le cCf dDf hI1 hI hk) hcp1 (by omega)
  -- the table
  have a2 : sE * (Ct * 2 ^ (Dt * ψ) * I ^ Dt) ≤ Ke * K1 * 2 ^ Ap * Pr := by
    rw [hK1, hAp, hPr]
    apply pre_into hn _ hcp1 (a := De + Din * Dg) (by omega)
    calc sE * (Ct * 2 ^ (Dt * ψ) * I ^ Dt) ≤ Ke * (n + 1) ^ De *
          (Cg * Kin ^ Dg * 2 ^ ((2 * Dg) * ψ) * (n + 1) ^ (Din * Dg)) :=
          Nat.mul_le_mul hE (s5_le cCt dDt hI1 hI hk)
      _ = Ke * (Cg * Kin ^ Dg) * 2 ^ ((2 * Dg) * ψ) * (n + 1) ^ (De + Din * Dg) := by rw [pow_add]; ring
  -- the overhead
  have a3 : Co * 2 ^ (Do * ψ) * I ^ Do ≤ K1 * 2 ^ Ap * Pr := by
    rw [hK1, hAp, hPr]
    exact pre_into hn (s5_le cCo dDo hI1 hI hk) hcp1 (by omega)
  -- the out machine
  have a4 : OC * (W + 1) ^ OD ≤ K4 * 2 ^ Ap * Pr := by
    rw [hK4, hAp, hPr]
    exact pre_into hn (out_le cOC dOD cCw dDw hW hI1 hI hk) hcp2 (by omega)
  -- the points
  have a5 : nP * (Cp * (n + 1) ^ Dp) ≤ Kp * Cg * 2 ^ (Dq + Dg) * Mn := by
    rw [hMn]
    apply main_into hn
    have hp : (n + 1) ^ Dp ≤ (n + 1) ^ Dg := Nat.pow_le_pow_right (by omega) dDp
    calc nP * (Cp * (n + 1) ^ Dp) ≤ Kp * 2 ^ (n - k / 4) * (n + 1) ^ Dq * (Cg * (n + 1) ^ Dg) :=
          Nat.mul_le_mul hP (Nat.mul_le_mul cCp hp)
      _ = Kp * Cg * 2 ^ (n - k / 4) * (n + 1) ^ (Dq + Dg) := by rw [pow_add]; ring
  have e1 : c5v Cg Dg Din De Dq Kin Ke Kp * (Pr + Mn) = K1 * 2 ^ Ap * Pr + Ke * K1 * 2 ^ Ap * Pr +
      K1 * 2 ^ Ap * Pr + K4 * 2 ^ Ap * Pr + 2 ^ Ap * Pr + 2 ^ Ap * Pr + Kp * Cg * 2 ^ (Dq + Dg) * Mn +
      (kPre Cg Dg Kin Ke * 2 ^ Ap * Mn + Kp * Cg * 2 ^ (Dq + Dg) * Pr) := by
    unfold c5v kPre; rw [← hAp, ← hK1, ← hK4]; ring
  rw [← hPr, ← hMn, e1]
  omega

end Arith

/-! ## S6 -/

section S6
variable (Sw : SymWords)
    (X : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SeedsWS2 l F kclk coef A a ha Sw)
    (bridgeT : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      SeedsWS2 l F kclk coef A a ha Sw → SeedsProg4 l F kclk coef A a ha Sw)
    (front : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      FrontPh3 l F kclk coef A a ha Sw (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)))
    (o : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t)
    (sc : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t → Bool)
    (O : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      OutMachine2 (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t (o l F kclk coef A a ha) (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tN (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tD (sc l F kclk coef A a ha))

/-- **The final pass's envelope** `E₅` from the exponents (fixed before `F`). -/
def e5 (Dg Din De Dq : ℕ) : Envelope where
  sigma := 0
  callDeg := 0
  Amain := Dq + Dg
  Atable := 0
  Asel := 0
  csel := 0
  Apre := De + Din * Dg + Din * (Dg * Dg)
  cpsi := 2 * Dg + Dg * Dg

/-- **S6's `fits`** at `E₅ = e5 …` (before `F`), `CD₅ = 1`, `c₅ = c5v …` (after `F`). -/
theorem s6_fits (U : S6Uni Sw X bridgeT front o sc O) (h1 : ∀ l, FpInBound l) (h2 : ∀ l, SeedCountBound l)
    (h3 : ∀ l, PtCountBound l) :
    S6Fits Sw X bridgeT front o sc O (fun l fe => e5 (U.Dg l fe) (dIn h1 l fe) (dE h2 l fe) (dQ h3 l fe))
      (fun _ _ => 1)
      (fun l fe F => c5v (U.Cg l fe F) (U.Dg l fe) (dIn h1 l fe) (dE h2 l fe) (dQ h3 l fe) (kIn h1 l F) (kE h2 l F)
        (kP h3 l F)) := by
  intro l fe F hfe _ hCD kclk coef A a ha
  subst hfe
  unfold FitsRes
  intro r
  obtain ⟨dDf, dDw, dDt, dDp, dDo, dOD⟩ := U.hD l F kclk coef A a ha
  obtain ⟨cCf, cCw, cCt, cCp, cCo, cOC⟩ := U.hC l F kclk coef A a ha
  obtain ⟨-, -, -, -, -, hs, -⟩ := r.2
  obtain ⟨-, hr2, hr4, -⟩ := hs
  have hn : 1 ≤ r.1.n := by omega
  have hCD1 : 1 ≤ F.CD := hCD
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf r.1.n ≤ ((gate0 l F).budget kclk coef A a ha).psiOf r.1.n :=
    le_trans (Nat.le_add_right _ _) (FinalPass.SymFr.kL_le_loadPsi F.CD _ (Nat.clog 2 (r.1.n + 2)) _ _ hCD1)
  exact fits_arith hn hk (kIn_spec h1 l F kclk coef A a ha r) (Nat.le_add_left _ _) (kE_spec h2 l F kclk coef A a ha r)
    (kP_spec h3 l F kclk coef A a ha r) ((front l F kclk coef A a ha).W_le r) dDf dDw dDt dDp dDo dOD
    cCf cCw cCt cCp cCo cOC

/-- **S6's target** (`S6Uni → S6Out`) from the three request-size bounds. -/
noncomputable def s6Target (h1 : ∀ l, FpInBound l) (h2 : ∀ l, SeedCountBound l) (h3 : ∀ l, PtCountBound l) :
    S6Target Sw X bridgeT front o sc O := fun U =>
  ⟨fun l fe => e5 (U.Dg l fe) (dIn h1 l fe) (dE h2 l fe) (dQ h3 l fe), fun _ _ => 1,
    fun l fe F => c5v (U.Cg l fe F) (U.Dg l fe) (dIn h1 l fe) (dE h2 l fe) (dQ h3 l fe) (kIn h1 l F) (kE h2 l F)
      (kP h3 l F), s6_fits Sw X bridgeT front o sc O U h1 h2 h3⟩

end S6

end NearCubicWires.WireExponent3_5.PrimAsm.S6Fit
