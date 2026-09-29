import Proof.Wire_3_5.FinalPass.Core7

/-! # S5Core, part 8: the request's facts the core needs (P3:3044-3048, 3083-3086)

* **`Sd.R.fpDen_ltR`**: the printed denominator fits the width, `fpDen r < 2^{Tf r}` (`FrontOut.numW` at `Den`; as
  `ptv_lt`: `Den ≤ |centers|·|seeds|·Q·v` with `v` the list seeds (SYM) or the primes below the cutoff (THR));
* **`fpIn_shape`**: the final pass's input starts `1^L 0 bits mb` with `L = natBitLength n`, `|bits| = L` and `mb`
  the THR flag (the request word's head, `reqW`), and `fpIn_len`;
* **`sym_blank_thr`**: at a THR request the SYM slots of `frontWordsW2` are blank.

Paper quantities: the printed denominator and its width (P3:3044-3048), the request's mode (P3:3083-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd.R
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The printed denominator fits the width.** -/
theorem fpDen_ltR (r : FReq l F kclk coef A a ha) :
    Seams.fpDen l F kclk coef A a ha r < 2 ^ Tf l F kclk coef A a ha r := by
  have h2 := n2_le_Tf l F kclk coef A a ha r
  have h1 : 1 < 2 ^ Tf l F kclk coef A a ha r := Nat.one_lt_two_pow (by omega)
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
  show max (NumDen.denRaw (callInputs l F kclk coef A a ha) (gate0 l F).alg _) 1 < _
  rcases Nat.lt_or_ge 1 (NumDen.denRaw (callInputs l F kclk coef A a ha) (gate0 l F).alg
    ⟨n, mode, a', ha', Cs, carriers, translation⟩) with hlt | hle
  swap
  · rw [max_eq_right hle]; exact h1
  rw [max_eq_left hlt.le]
  unfold Tf
  cases mode with
  | sym =>
    simp only [NumDen.denRaw, dif_pos hs, NumDen.symDen, Fintype.card_prod]
    have hQ := PrimAsm.CallIndexR.symCount_leR l F kclk coef A a ha n hs ha' Cs carriers hd hcar
    have hQ2 : SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ≤
        2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4 +
          8192 * PrimAsm.CallIndexR.symKI F.cr * (n + 2) ^ (PrimAsm.CallIndexR.symZI l F.filterErrDeg + 2)) := by
      rw [pow_add]
      refine hQ.trans (Nat.mul_le_mul_left _ ?_)
      exact le_two_pow_of le_rfl
    have hV := vsym_le l F kclk coef A a ha n ha' Cs carriers hd hcar
    rw [show ∀ x y z w : ℕ, x * (y * z) * w = x * y * w * z from fun x y z w => by ring]
    refine lt_of_le_of_lt (mul4_le hcc (hgap .sym) hQ2 (le_two_pow_of hV)) (Nat.pow_lt_pow_right (by norm_num) ?_)
    have hlt := expo_ltR n (PrimAsm.CallIndexR.gapK F.cr) (8192 * PrimAsm.CallIndexR.symKI F.cr)
      (2 * PrimAsm.CallIndexR.flatK F.cr) (PrimAsm.CallIndexR.gapZR l F.filterErrDeg)
      (PrimAsm.CallIndexR.symZI l F.filterErrDeg + 2) (ZV l) (ZT l F) (by unfold ZT; omega) (by unfold ZT; omega)
      (by unfold ZT; omega) hZ2
    have hk := Nat.mul_le_mul_right ((n + 2) ^ ZT l F) (hKT (8192 * PrimAsm.CallIndexR.symKI F.cr) (by omega))
    omega
  | thr =>
    simp only [NumDen.denRaw, dif_pos hs, NumDen.thrDen]
    have hQ := PrimAsm.CallIndexR.thrCount_leR l F kclk coef A a ha n hs ha' Cs hd
    have hQ2 : SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
        2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4 +
          8192 * PrimAsm.CallIndexR.gapK F.cr * (n + 2) ^ (PrimAsm.CallIndexR.thrZI l F.filterErrDeg + 2)) := by
      rw [pow_add]
      refine hQ.trans (Nat.mul_le_mul_left _ ?_)
      exact le_two_pow_of le_rfl
    have hcut := PrimAsm.CallIndex.cut_le l F kclk coef A a ha n hs ha' Cs hd
    have hpr := card_prime_le (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    have hK := PrimAsm.CallIndexR.flatK_pos F.cr
    have hp1 : 1 ≤ (n + 2) ^ (10 * PrimAsm.CallIndex.algX l + 32) := Nat.one_le_pow _ _ (by omega)
    have hpz : (n + 2) ^ (10 * PrimAsm.CallIndex.algX l + 32) ≤ (n + 2) ^ ZV l :=
      Nat.pow_le_pow_right (by omega) (by unfold ZV; omega)
    have hV : Fintype.card (PrimeIndex (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs
        (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤
        2 * PrimAsm.CallIndexR.flatK F.cr * (n + 2) ^ ZV l := by
      have hm := Nat.mul_le_mul_right ((n + 2) ^ ZV l) hK
      have e : 2 * PrimAsm.CallIndexR.flatK F.cr * (n + 2) ^ ZV l =
          2 * (PrimAsm.CallIndexR.flatK F.cr * (n + 2) ^ ZV l) := by ring
      omega
    rw [show ∀ x y z w : ℕ, x * y * z * w = y * z * w * x from fun x y z w => by ring]
    refine lt_of_le_of_lt (mul4_le hcc (hgap .thr) hQ2 (le_two_pow_of hV)) (Nat.pow_lt_pow_right (by norm_num) ?_)
    have hlt := expo_ltR n (PrimAsm.CallIndexR.gapK F.cr) (8192 * PrimAsm.CallIndexR.gapK F.cr)
      (2 * PrimAsm.CallIndexR.flatK F.cr) (PrimAsm.CallIndexR.gapZR l F.filterErrDeg)
      (PrimAsm.CallIndexR.thrZI l F.filterErrDeg + 2) (ZV l) (ZT l F) (by unfold ZT; omega) (by unfold ZT; omega)
      (by unfold ZT; omega) hZ2
    have hk := Nat.mul_le_mul_right ((n + 2) ^ ZT l F) (hKT (8192 * PrimAsm.CallIndexR.gapK F.cr) (by omega))
    omega

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R
