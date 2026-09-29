import Proof.Wire_3_5.FinalPass.SymOcc4

/-! # The SYM child request's precondition, part 1: the request's numbers

At a SYM call the compiler request's numbers fit alg:compiler's precondition (P3:1882-1900): the stacked fields
`h·Q'·d ≤ pr` (**`hqd_sym`**), the scaled coefficients `N^{16}·2^{8ℓ}·2^{Q'} ≤ 2^{pr}` (**`coef_sym`**), and the pool's
fits at `h = dH(n+1)^{eH}` (**`fits_sym`**, from `SymPool`); all under constraints on the SYM constants that read
the literals and `fe` alone (`capK c_r ≤ 2^{48}(n+1)^{48}` since `c_r ≤ k/4 ≤ n`).
* `kL_le_n`, `sqrtCap_le`, **`hqd_sym`**, **`coef_sym`**, **`fits_sym`**.
Paper quantities of the main types: the child request's `h, Q', d, pr` and the pool's fields. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine

section Gate
variable (l : Literals) (F : GateFree l)

/-- `k + L ≤ 2(n+1)` at a call. -/
theorem kL_le_n (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation)) :
    ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) ≤ 2 * (n + 1) := by
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ n := hcall.2.2.2.2.2.2.kq
  have hL : Nat.clog 2 (n + 2) ≤ n + 1 := Nat.clog_le_of_le_pow (by
    have := Nat.lt_two_pow_self (n := n + 1)
    rw [pow_succ] at this ⊢; omega)
  omega

/-- `⌊√B_S⌋ + L ≤ 2^{49+Z}(n+1)^{48+Z}` at a call (`c_r ≤ k/4 ≤ n`). -/
theorem sqrtCap_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n) + Nat.clog 2 (n + 2) ≤
      2 ^ (49 + CallIndexR.capZR l) * (n + 1) ^ (48 + CallIndexR.capZR l) := by
  have hc : ((gate0 l F).budget kclk coef A a ha).capOf .sym n ≤ CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l :=
    CallIndexR.cap_leR l F.cr .sym n
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ n := hcall.2.2.2.2.2.2.kq
  have hcr := cr_le_k l F kclk coef A a ha hs
  have hkL := kL_le_n l F kclk coef A a ha ha' Cs carriers translation hcall
  have hsq := Nat.sqrt_le_self (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hL : Nat.clog 2 (n + 2) ≤ n + 1 := Nat.clog_le_of_le_pow (by
    have := Nat.lt_two_pow_self (n := n + 1)
    rw [pow_succ] at this ⊢; omega)
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = CallIndexR.capZR l := ⟨_, rfl⟩
  rw [← hZ] at hc ⊢
  have h1 : CallIndexR.capK F.cr ≤ 2 ^ 48 * (n + 1) ^ 48 := by
    calc CallIndexR.capK F.cr = (2 * F.cr + 2) ^ 48 := rfl
      _ ≤ (2 * (n + 1)) ^ 48 := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ 48 * (n + 1) ^ 48 := by rw [mul_pow]
  have h2 : (n + 2) ^ Z ≤ 2 ^ Z * (n + 1) ^ Z := by
    calc (n + 2) ^ Z ≤ (2 * (n + 1)) ^ Z := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ Z * (n + 1) ^ Z := by rw [mul_pow]
  have h3 : CallIndexR.capK F.cr * (n + 2) ^ Z ≤ 2 ^ (48 + Z) * (n + 1) ^ (48 + Z) := by
    calc _ ≤ (2 ^ 48 * (n + 1) ^ 48) * (2 ^ Z * (n + 1) ^ Z) := Nat.mul_le_mul h1 h2
      _ = _ := by rw [pow_add, pow_add]; ring
  have h4 : n + 1 ≤ (n + 1) ^ (48 + Z) := Nat.le_self_pow (by omega) _
  have h5 : 1 ≤ 2 ^ (48 + Z) := Nat.one_le_two_pow
  have e : 2 ^ (49 + Z) * (n + 1) ^ (48 + Z) = 2 ^ (48 + Z) * (n + 1) ^ (48 + Z) + 2 ^ (48 + Z) * (n + 1) ^ (48 + Z) := by
    rw [show 49 + Z = (48 + Z) + 1 by ring, pow_succ]; ring
  rw [e]
  have h6 : n + 1 ≤ 2 ^ (48 + Z) * (n + 1) ^ (48 + Z) := h4.trans (Nat.le_mul_of_pos_left _ h5)
  generalize 2 ^ (48 + Z) * (n + 1) ^ (48 + Z) = U at h3 h6 ⊢
  generalize CallIndexR.capK F.cr * (n + 2) ^ Z = V at hc h3
  omega

/-- **`h·Q'·d ≤ pr`** at a SYM call. -/
theorem hqd_sym (c : SymC) (hdP : c.dH * c.dQ * c.dD * 2 ^ (50 + CallIndexR.capZR l) ≤ c.dP)
    (heP : c.eH + 49 + CallIndexR.capZR l ≤ c.eP) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3 *
        (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2 *
        symDF c (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) ≤
      (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5 := by
  have hQ := Qp_eq l F c kclk coef A a ha Cs carriers hs
  have hkL := kL_le_n l F kclk coef A a ha ha' Cs carriers translation hcall
  have hsc := sqrtCap_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  rw [hQ]
  show c.dH * (n + 1) ^ c.eH * (c.dQ * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) *
      (c.dD * (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n) + Nat.clog 2 (n + 2))) ≤
    c.dP * (n + 1) ^ c.eP
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = CallIndexR.capZR l := ⟨_, rfl⟩
  rw [← hZ] at hdP heP hsc
  obtain ⟨X, hX⟩ : ∃ X, X = ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n) + Nat.clog 2 (n + 2) :=
    ⟨_, rfl⟩
  rw [← hX] at hkL ⊢
  rw [← hY] at hsc ⊢
  have hp : (n + 1) ^ c.eH * (n + 1) * (n + 1) ^ (48 + Z) ≤ (n + 1) ^ c.eP := by
    rw [← pow_succ, ← pow_add]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  calc c.dH * (n + 1) ^ c.eH * (c.dQ * X) * (c.dD * Y)
      ≤ c.dH * (n + 1) ^ c.eH * (c.dQ * (2 * (n + 1))) * (c.dD * (2 ^ (49 + Z) * (n + 1) ^ (48 + Z))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hkL)) (Nat.mul_le_mul_left _ hsc)
    _ = c.dH * c.dQ * c.dD * (2 * 2 ^ (49 + Z)) * ((n + 1) ^ c.eH * (n + 1) * (n + 1) ^ (48 + Z)) := by ring
    _ = c.dH * c.dQ * c.dD * 2 ^ (50 + Z) * ((n + 1) ^ c.eH * (n + 1) * (n + 1) ^ (48 + Z)) := by
        rw [show 50 + Z = (49 + Z) + 1 by ring, pow_succ]; ring
    _ ≤ c.dP * (n + 1) ^ c.eP := Nat.mul_le_mul hdP hp

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

