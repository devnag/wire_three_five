import Proof.Wire_3_5.FinalPass.SdI11
import Proof.Wire_3_5.Primitive.Writers.CallIndexR

/-! # S4 v2, part R2: the numbers' width with the degree on `(l, fe)` alone (P3:3044-3048, 3114-3115)

S4 v1's exponents (`Sd.ZV`, `Sd.ZT`, `Sd.C1m`) come from `CallIndex`, whose cap exponent `capZ l F` carries `51·c_r`,
so S4's degrees depend on `F`. Here the same width is bounded through `CallIndexR` (the exponents on `l` and the
filter error degree `fe` only, `c_r` in the coefficients: `gapSeed_leR`, `flatSeed_leR`, `symCount_leR`,
`thrCount_leR`): **`ZV`**, **`ZT`** on `(l, fe)`, **`KT`** on `F`, the width **`Tf r = KT·(n+2)^{ZT}`**,
**`ptv_lt`** (`ptCount·vmax < 2^{Tf r}`), **`fpNum_lt`**, **`n2_le_Tf`**. Namespace `Sd.R`: S4 v2's names shadow v1's.

Paper quantity of the main type: the width of the printed numerator, its powers of `n` fixed before the gate
(P3:3044-3048, 3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd.R
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split

/-- **The exponent sum below the width**, the coefficients inside. -/
theorem expo_ltR (n g q v a b c Z : ℕ) (ha : a ≤ Z) (hb : b ≤ Z) (hc : c ≤ Z) (h2 : 2 ≤ Z) :
    n + g * (n + 2) ^ a + ((2 * (n * n) + 1) + q * (n + 2) ^ b) + v * (n + 2) ^ c <
      (g + q + v + 8) * (n + 2) ^ Z := by
  have hN : 1 ≤ n + 2 := by omega
  have hy2 : (n + 2) ^ 2 ≤ (n + 2) ^ Z := Nat.pow_le_pow_right hN h2
  have ha' := Nat.mul_le_mul_left g (Nat.pow_le_pow_right hN ha)
  have hb' := Nat.mul_le_mul_left q (Nat.pow_le_pow_right hN hb)
  have hc' := Nat.mul_le_mul_left v (Nat.pow_le_pow_right hN hc)
  have hsq : n * n + 4 * n + 4 = (n + 2) ^ 2 := by ring
  have e : (g + q + v + 8) * (n + 2) ^ Z = g * (n + 2) ^ Z + q * (n + 2) ^ Z + v * (n + 2) ^ Z + 8 * (n + 2) ^ Z := by
    ring
  rw [e]
  generalize (n + 2) ^ Z = y at hy2 ha' hb' hc' ⊢
  generalize (n + 2) ^ 2 = s at hsq hy2
  generalize n * n = m at hsq ⊢
  omega

section Family
variable (l : Literals) (F : GateFree l)

/-- The per-point values' exponent (both modes), on `l`. -/
noncomputable def ZV : ℕ := PrimAsm.CallIndexR.flatZR l + 14 * PrimAsm.CallIndex.algX l + 32

/-- **The width's exponent**, on `(l, fe)`. -/
noncomputable def ZT : ℕ :=
  PrimAsm.CallIndexR.gapZR l F.filterErrDeg + PrimAsm.CallIndexR.symZI l F.filterErrDeg +
    PrimAsm.CallIndexR.thrZI l F.filterErrDeg + ZV l + 4

/-- **The width's coefficient**, on `F` (`c_r` enters here). -/
noncomputable def KT : ℕ :=
  PrimAsm.CallIndexR.gapK F.cr + 8192 * (PrimAsm.CallIndexR.symKI F.cr + PrimAsm.CallIndexR.gapK F.cr) +
    2 * PrimAsm.CallIndexR.flatK F.cr + 8

variable (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The width of the numbers** at a request: `KT·(n+2)^{ZT}`. -/
noncomputable def Tf (r : FReq l F kclk coef A a ha) : ℕ := KT l F * (r.1.n + 2) ^ ZT l F

theorem vsym_le (n : ℕ) {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (hcar : carriers.length ≤ 2) :
    Fintype.card (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).FlatSeed ≤
      2 * PrimAsm.CallIndexR.flatK F.cr * (n + 2) ^ ZV l := by
  have h := PrimAsm.CallIndexR.flatSeed_leR l F kclk coef A a ha n ha' Cs carriers hd hcar
  have h2 : (n + 2) ^ PrimAsm.CallIndexR.flatZR l ≤ (n + 2) ^ ZV l :=
    Nat.pow_le_pow_right (by omega) (by unfold ZV; omega)
  have h3 := Nat.mul_le_mul_left (PrimAsm.CallIndexR.flatK F.cr) h2
  have e : 2 * PrimAsm.CallIndexR.flatK F.cr * (n + 2) ^ ZV l =
      2 * (PrimAsm.CallIndexR.flatK F.cr * (n + 2) ^ ZV l) := by ring
  omega

theorem vthr_le (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) *
        Fintype.card (PrimeIndex (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤
      2 * PrimAsm.CallIndexR.flatK F.cr * (n + 2) ^ ZV l := by
  have h1 := PrimAsm.CallIndex.thrEq_le l F kclk coef A a ha n hs ha' Cs hd
  have h2 := PrimAsm.CallIndex.cut_le l F kclk coef A a ha n hs ha' Cs hd
  have h3 := card_prime_le (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
    (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
  have hK := PrimAsm.CallIndexR.flatK_pos F.cr
  have hp : 1 ≤ (n + 2) ^ (10 * PrimAsm.CallIndex.algX l + 32) := Nat.one_le_pow _ _ (by omega)
  have e : (n + 2) ^ ZV l =
      (n + 2) ^ (PrimAsm.CallIndexR.flatZR l) * ((n + 2) ^ (PrimAsm.CallIndex.algX l * 4) *
        (n + 2) ^ (10 * PrimAsm.CallIndex.algX l + 32)) := by
    rw [← pow_add, ← pow_add]; unfold ZV; ring_nf
  have hf : 1 ≤ (n + 2) ^ (PrimAsm.CallIndexR.flatZR l) := Nat.one_le_pow _ _ (by omega)
  rw [e]
  generalize (n + 2) ^ (PrimAsm.CallIndexR.flatZR l) = f at hf ⊢
  generalize (n + 2) ^ (PrimAsm.CallIndex.algX l * 4) = g at h1 ⊢
  generalize (n + 2) ^ (10 * PrimAsm.CallIndex.algX l + 32) = c at h2 hp ⊢
  generalize PrimAsm.CallIndexR.flatK F.cr = K at hK ⊢
  calc _ ≤ g * (2 * c) := Nat.mul_le_mul h1 (by omega)
    _ = 1 * 1 * (2 * (g * c)) := by ring
    _ ≤ K * f * (2 * (g * c)) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hK hf)
    _ = 2 * K * (f * (g * c)) := by ring

/-- **The numbers' width**: `ptCount·vmax < 2^{Tf r}`. -/
theorem ptv_lt (r : FReq l F kclk coef A a ha) :
    Seams.ptCount l F kclk coef A a ha r * Seams.vmax l F kclk coef A a ha r < 2 ^ Tf l F kclk coef A a ha r := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  have hd : ∀ i, mode.descriptionBits (Cs i) ≤ (n + 1) ^ 26 := hcall.2.2.1
  have hcar : carriers.length ≤ 2 := hcall.2.2.2.1
  have hkh : SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) ≤ n * n :=
    (star_le ((callInputs l F kclk coef A a ha).starParams n hs)).2.2.2.2.2.2.2.2.2
  have hkh' : (5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4 ≤ 2 * (n * n) + 1 := by
    generalize n * n = m at hkh ⊢
    omega
  have hcc : Fintype.card {c // ((callInputs l F kclk coef A a ha).starParams n hs).IsCenter
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) c} ≤ 2 ^ n := by
    rw [StarParams.card_centers]; exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have hZ2 : 2 ≤ ZT l F := by unfold ZT; omega
  have hgap : ∀ m : Mode, Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams m n)) ≤
      2 ^ (PrimAsm.CallIndexR.gapK F.cr * (n + 2) ^ PrimAsm.CallIndexR.gapZR l F.filterErrDeg) := fun m =>
    le_two_pow_of (PrimAsm.CallIndexR.gapSeed_leR l F kclk coef A a ha m n)
  have hKT : ∀ q : ℕ, q ≤ 8192 * (PrimAsm.CallIndexR.symKI F.cr + PrimAsm.CallIndexR.gapK F.cr) →
      PrimAsm.CallIndexR.gapK F.cr + q + 2 * PrimAsm.CallIndexR.flatK F.cr + 8 ≤ KT l F := fun q hq => by
    unfold KT; omega
  unfold Tf
  cases mode with
  | sym =>
    simp only [Seams.ptCount, Seams.vmax, Seams.ptCountOf, Seams.vmaxOf, dif_pos hs]
    have hQ := PrimAsm.CallIndexR.symCount_leR l F kclk coef A a ha n hs ha' Cs carriers hd hcar
    have hQ2 : SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ≤
        2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4 +
          8192 * PrimAsm.CallIndexR.symKI F.cr * (n + 2) ^ (PrimAsm.CallIndexR.symZI l F.filterErrDeg + 2)) := by
      rw [pow_add]
      refine hQ.trans (Nat.mul_le_mul_left _ ?_)
      exact le_two_pow_of le_rfl
    have hV := vsym_le l F kclk coef A a ha n ha' Cs carriers hd hcar
    refine lt_of_le_of_lt (mul4_le hcc (hgap .sym) hQ2 (le_two_pow_of hV)) (Nat.pow_lt_pow_right (by norm_num) ?_)
    have hlt := expo_ltR n (PrimAsm.CallIndexR.gapK F.cr) (8192 * PrimAsm.CallIndexR.symKI F.cr)
      (2 * PrimAsm.CallIndexR.flatK F.cr) (PrimAsm.CallIndexR.gapZR l F.filterErrDeg)
      (PrimAsm.CallIndexR.symZI l F.filterErrDeg + 2) (ZV l) (ZT l F) (by unfold ZT; omega) (by unfold ZT; omega)
      (by unfold ZT; omega) hZ2
    have hk := Nat.mul_le_mul_right ((n + 2) ^ ZT l F) (hKT (8192 * PrimAsm.CallIndexR.symKI F.cr) (by omega))
    have e : 8192 * PrimAsm.CallIndexR.symKI F.cr * (n + 2) ^ (PrimAsm.CallIndexR.symZI l F.filterErrDeg + 2) =
      8192 * PrimAsm.CallIndexR.symKI F.cr * (n + 2) ^ (PrimAsm.CallIndexR.symZI l F.filterErrDeg + 2) := rfl
    omega
  | thr =>
    simp only [Seams.ptCount, Seams.vmax, Seams.ptCountOf, Seams.vmaxOf, dif_pos hs]
    have hQ := PrimAsm.CallIndexR.thrCount_leR l F kclk coef A a ha n hs ha' Cs hd
    have hQ2 : SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
        2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4 +
          8192 * PrimAsm.CallIndexR.gapK F.cr * (n + 2) ^ (PrimAsm.CallIndexR.thrZI l F.filterErrDeg + 2)) := by
      rw [pow_add]
      refine hQ.trans (Nat.mul_le_mul_left _ ?_)
      exact le_two_pow_of le_rfl
    have hV := vthr_le l F kclk coef A a ha n hs ha' Cs hd
    refine lt_of_le_of_lt (mul4_le hcc (hgap .thr) hQ2 (le_two_pow_of hV)) (Nat.pow_lt_pow_right (by norm_num) ?_)
    have hlt := expo_ltR n (PrimAsm.CallIndexR.gapK F.cr) (8192 * PrimAsm.CallIndexR.gapK F.cr)
      (2 * PrimAsm.CallIndexR.flatK F.cr) (PrimAsm.CallIndexR.gapZR l F.filterErrDeg)
      (PrimAsm.CallIndexR.thrZI l F.filterErrDeg + 2) (ZV l) (ZT l F) (by unfold ZT; omega) (by unfold ZT; omega)
      (by unfold ZT; omega) hZ2
    have hk := Nat.mul_le_mul_right ((n + 2) ^ ZT l F) (hKT (8192 * PrimAsm.CallIndexR.gapK F.cr) (by omega))
    omega

/-- **The printed numerator fits the width.** -/
theorem fpNum_lt (r : FReq l F kclk coef A a ha) : Seams.fpNum l F kclk coef A a ha r < 2 ^ Tf l F kclk coef A a ha r :=
  lt_of_le_of_lt (fpNum_le l F kclk coef A a ha r) (ptv_lt l F kclk coef A a ha r)

theorem n2_le_Tf (r : FReq l F kclk coef A a ha) : r.1.n + 2 ≤ Tf l F kclk coef A a ha r := by
  unfold Tf
  have h1 : r.1.n + 2 ≤ (r.1.n + 2) ^ ZT l F := Nat.le_self_pow (by unfold ZT; omega) _
  have h2 : (r.1.n + 2) ^ ZT l F ≤ KT l F * (r.1.n + 2) ^ ZT l F := Nat.le_mul_of_pos_left _ (by unfold KT; omega)
  omega

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R
