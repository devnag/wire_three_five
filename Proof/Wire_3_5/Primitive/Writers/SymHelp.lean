import Proof.Wire_3_5.Primitive.Writers.SymReady
import Proof.Wire_3_5.Primitive.Writers.HashFam

/-! # SYM leaf, part 9: the SYM call's sizes against the dimension

At a SYM call of the gate's family (`P = starParams n`, `L = ⌈log₂(n+2)⌉`, `k = kOf n`, the SYM cap `B_S`):

* **`sfam_mS`**: `m_S = k + L + K_F·L² + T` (`NumsXS.mS` at `D₂' = 26`, `K₀ = 6`);
* **`toQ`**: `(n+2)^d·2^{aL}·2^k·2^T ≤ 2^{m_S}` whenever `d + a ≤ K_F` (every size of the call is below the dimension);
* `sb_le` (the SYM filter's seed length `≤ 6000((26 + Z + fe)L + ⌈log₂(capK+1)⌉ + 4)`), `fbv_le` (the flat list's
  seed length `≤ (4Z + 4D₂ + 160)L + 888 + 4⌈log₂ capK⌉ + 4⌈log₂ C₂⌉`).

Paper quantities of the main types: the SYM writer's dimension `2^{m_S}` against the call's seeds and slices
(P3:3089-3108). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Transfer

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The SYM dimension**: `m_S = k + L + K_F·L² + T`. -/
theorem sfam_mS {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) (KF : ℕ) :
    NumsXS.mS KF ((callInputs l F kclk coef A a ha).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l)
        (gateCap l) 26 6 =
      ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) + KF * Nat.clog 2 (n + 2) ^ 2 +
        SymSizes.tSOf (((gate0 l F).budget kclk coef A a ha).capOf .sym n) 26 6 (Nat.clog 2 (n + 2)) := by
  unfold NumsXS.mS PrimThrW.Shell2.mOfT NumsX.mOf
  rw [HashFam.fam_two_kh l F kclk coef A a ha hs]
  rfl

/-- The SYM cap: `B_S ≤ capK c_r·(n+2)^Z`. -/
theorem sfam_capS (n : ℕ) :
    ((gate0 l F).budget kclk coef A a ha).capOf .sym n ≤ CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l :=
  CallIndexR.cap_leR l F.cr .sym n

end Call

/-- **Every size is below the dimension**: `(n+2)^d·2^{aL}·2^k·2^T ≤ 2^{k + L + K_F L² + T}` for `d + a ≤ K_F`. -/
theorem toQ (n d a k T KF : ℕ) (hda : d + a ≤ KF) :
    (n + 2) ^ d * 2 ^ (a * Nat.clog 2 (n + 2)) * 2 ^ k * 2 ^ T ≤
      2 ^ (k + Nat.clog 2 (n + 2) + KF * Nat.clog 2 (n + 2) ^ 2 + T) := by
  obtain ⟨L, hL⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hL]
  have hn : n + 2 ≤ 2 ^ L := by rw [hL]; exact Nat.le_pow_clog (by norm_num) _
  have hL1 : 1 ≤ L := by rw [hL]; exact Nat.clog_pos (by norm_num) (by omega)
  have h1 : (n + 2) ^ d ≤ 2 ^ (d * L) := by
    calc (n + 2) ^ d ≤ (2 ^ L) ^ d := Nat.pow_le_pow_left hn d
      _ = 2 ^ (d * L) := by rw [← pow_mul, mul_comm]
  have h2 : (d + a) * L ≤ KF * L ^ 2 := by
    have : (d + a) * L ≤ KF * L := Nat.mul_le_mul_right _ hda
    have : KF * L ≤ KF * L ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    omega
  calc (n + 2) ^ d * 2 ^ (a * L) * 2 ^ k * 2 ^ T ≤ 2 ^ (d * L) * 2 ^ (a * L) * 2 ^ k * 2 ^ T := by
        gcongr
    _ = 2 ^ ((d + a) * L + k + T) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The SYM filter's seed length. -/
theorem sb_le (n capS capK Z fe : ℕ) (hB : capS ≤ capK * (n + 2) ^ Z) :
    (SymDec.gP n capS (fe * Ledger.Lq n)).seedBits ≤
      6000 * ((26 + Z + fe) * Nat.clog 2 (n + 2) + Nat.clog 2 (capK + 1) + 4) := by
  have h := Filters.seedBits_le (SymDec.gP n capS (fe * Ledger.Lq n))
  obtain ⟨L, hL⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hn : n + 2 ≤ 2 ^ L := by rw [hL]; exact Nat.le_pow_clog (by norm_num) _
  have hlen : Nat.clog 2 (2 * (n + 1) ^ 26 + 1) ≤ 26 * L + 2 := by
    apply Nat.clog_le_of_le_pow
    have a1 : (n + 1) ^ 26 ≤ 2 ^ (26 * L) := by
      rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left (by omega) 26
    rw [pow_add]; have := Nat.one_le_two_pow (n := 26 * L); omega
  have hcap : Nat.clog 2 (capS + 1) ≤ Nat.clog 2 (capK + 1) + Z * L := by
    apply Nat.clog_le_of_le_pow
    have a1 : capK + 1 ≤ 2 ^ Nat.clog 2 (capK + 1) := Nat.le_pow_clog (by norm_num) _
    have a2 : (n + 2) ^ Z ≤ 2 ^ (Z * L) := by rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left hn Z
    have a3 : 1 ≤ (n + 2) ^ Z := Nat.one_le_pow _ _ (by omega)
    have a4 : capS + 1 ≤ (capK + 1) * (n + 2) ^ Z := by
      have e : (capK + 1) * (n + 2) ^ Z = capK * (n + 2) ^ Z + (n + 2) ^ Z := by ring
      omega
    rw [pow_add]
    exact le_trans a4 (Nat.mul_le_mul a1 a2)
  have heq : (SymDec.gP n capS (fe * Ledger.Lq n)).len = 2 * (n + 1) ^ 26 := rfl
  have hcq : (SymDec.gP n capS (fe * Ledger.Lq n)).cap = capS := rfl
  have heq2 : (SymDec.gP n capS (fe * Ledger.Lq n)).errExp = fe * L := by rw [hL]; rfl
  rw [heq, hcq, heq2] at h
  rw [← hL]
  have e : 6000 * ((26 + Z + fe) * L + Nat.clog 2 (capK + 1) + 4) =
      6000 * (26 * L + 2) + 6000 * (Nat.clog 2 (capK + 1) + Z * L) + 6000 * (fe * L) + 12000 := by ring
  omega

/-- The flat list's seed length. -/
theorem fbv_le (M B L cB cM Z D2 : ℕ) (hB : B ≤ 2 ^ (cB + Z * L)) (hM : M ≤ 2 ^ (cM + D2 * L)) :
    FlatNums.fbv M B (L + 5) ≤ (4 * Z + 4 * D2 + 160) * L + (4 * (cB + cM + 9) + 800) := by
  have h1 : Nat.clog 2 B ≤ cB + Z * L := Nat.clog_le_of_le_pow hB
  have h2 : Nat.clog 2 M ≤ cM + D2 * L := Nat.clog_le_of_le_pow hM
  have hr : FlatNums.rkv M B ≤ cB + Z * L + cM + D2 * L + 9 := by
    unfold FlatNums.rkv; exact max_le (by omega) (by omega)
  unfold FlatNums.fbv FlatNums.sbv FlatNums.wlv
  have hw : 2 * ((L + 5) / 2 / 2) + 1 - 1 ≤ L + 5 := by omega
  have hw2 : (2 * ((L + 5) / 2 / 2) + 1 - 1) * 160 ≤ (L + 5) * 160 := Nat.mul_le_mul_right _ hw
  have hs : (FlatNums.rkv M B + FlatNums.rkv M B + FlatNums.rkv M B) / 2 ≤ 2 * FlatNums.rkv M B := by omega
  have e : (4 * Z + 4 * D2 + 160) * L + (4 * (cB + cM + 9) + 800) =
      4 * (cB + Z * L + cM + D2 * L + 9) + (L + 5) * 160 := by ring
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SymFam
