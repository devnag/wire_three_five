import Lean
import Proof.Wire_3_5.FinalPass.SymSz1
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SymSz1Base


noncomputable section
set_option maxRecDepth 4096


/-! # The SYM free numbers (root #145 (ii)), part 3: `n_T`, `Q`, `ℓ` below `2^{O(k+L)}`

The SYM tape's `n_T = |GapSeed|·|FlatSeed|·Π_j(m_j+1)²` states (P3:3011-3016), the sample count `Q` of `samp:q`
(P3:2987-2988) and the seed field `ℓ = max(1, 2kh, ⌈log₂Q⌉)` (P3:2929-2941): at a SYM call each is `2^{O(k+L)}`
(resp. `O(k+L)`), with exponents of the literals and `fe` alone (`symKI_kL`: `c_r ≤ k/4`).

* `eN`, **`symNT_le`**; `eQ`, **`symCount_le`**; **`ell_le`**.

Paper quantities of the main types: `n_T`, `Q`, `ℓ` at a SYM call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-- The exponent of `n_T`. -/
noncomputable def eN (l : Literals) (fe : ℕ) : ℕ := cK + (CallIndexR.gapZR l fe + CallIndexR.flatZR l + 52 * 4)

/-- The exponent of `Q`. -/
noncomputable def eQ (l : Literals) (fe : ℕ) : ℕ := 1 + 13 + cK + (CallIndexR.symZI l fe + 2)

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **`n_T ≤ 2^{eN(k+L)}`** at a SYM call. -/
theorem symNT_le {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers ≤
      2 ^ (eN l F.filterErrDeg * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hcar : carriers.length ≤ 2 := hcall.2.2.2.1
  have hg := CallIndexR.gapSeed_leR l F kclk coef A a ha .sym n
  have hf := CallIndexR.flatSeed_leR l F kclk coef A a ha n ha' Cs carriers hd hcar
  have hst := CallIndex.symState_le l F kclk coef A a ha n hs ha' Cs hd
  have hidx : Fintype.card (SeedFix.SymIndex (callInputs l F kclk coef A a ha) hs Cs carriers) ≤
      CallIndexR.symKI F.cr * (n + 2) ^ (CallIndexR.gapZR l F.filterErrDeg + CallIndexR.flatZR l + 52 * 4) := by
    unfold SeedFix.SymIndex
    rw [Fintype.card_prod, Fintype.card_prod]
    calc _ ≤ (CallIndexR.gapK F.cr * (n + 2) ^ CallIndexR.gapZR l F.filterErrDeg) *
          (CallIndexR.flatK F.cr * (n + 2) ^ CallIndexR.flatZR l) * (n + 2) ^ (52 * 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul hg hf) hst
      _ = CallIndexR.symKI F.cr * (n + 2) ^ (CallIndexR.gapZR l F.filterErrDeg + CallIndexR.flatZR l + 52 * 4) := by
          unfold CallIndexR.symKI; rw [pow_add, pow_add]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hcard : Fintype.card (SeedFix.SymIndex (callInputs l F kclk coef A a ha) hs Cs carriers) =
      Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers := by
    rw [Fintype.card_congr (Enum.symIndexEquiv (callInputs l F kclk coef A a ha) hs Cs carriers), Fintype.card_fin]
  have hK := symKI_kL l F kclk coef A a ha hs
  have hN := pow_N_le n (CallIndexR.gapZR l F.filterErrDeg + CallIndexR.flatZR l + 52 * 4)
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = CallIndexR.gapZR l F.filterErrDeg + CallIndexR.flatZR l + 52 * 4 := ⟨_, rfl⟩
  rw [← hZ] at hidx hN
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hK
  rw [← hLd] at hN
  rw [← hKd, ← hLd, ← hcard]
  have hN' : 2 ^ (Z * L) ≤ 2 ^ (Z * (K + L)) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  calc _ ≤ _ := hidx
    _ ≤ 2 ^ (cK * (K + L)) * 2 ^ (Z * (K + L)) := Nat.mul_le_mul hK (hN.trans hN')
    _ = 2 ^ (eN l F.filterErrDeg * (K + L)) := by rw [← pow_add, ← Nat.add_mul, hZ]; rfl

/-- **`Q ≤ 2^{eQ(k+L)}`** at a SYM call. -/
theorem symCount_le {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ≤
      2 ^ (eQ l F.filterErrDeg * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hcar : carriers.length ≤ 2 := hcall.2.2.2.1
  have hQ := CallIndexR.symCount_leR l F kclk coef A a ha n hs ha' Cs carriers hd hcar
  have hx := CallIndexR.kh_exp_le l F kclk coef A a ha n hs
  have hL1 := one_le_L n
  have hK := symKI_kL l F kclk coef A a ha hs
  have hN := pow_N_le n (CallIndexR.symZI l F.filterErrDeg + 2)
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd] at hx
  rw [← hKd, ← hLd] at hK
  rw [← hLd] at hN hL1
  rw [← hKd, ← hLd]
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = CallIndexR.symZI l F.filterErrDeg + 2 := ⟨_, rfl⟩
  rw [← hZ] at hQ hN
  have h1 : 2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4) ≤ 2 ^ (1 * (K + L)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 8192 ≤ 2 ^ (13 * (K + L)) := by
    calc 8192 = 2 ^ 13 := by norm_num
      _ ≤ 2 ^ (13 * (K + L)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN' : 2 ^ (Z * L) ≤ 2 ^ (Z * (K + L)) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  calc _ ≤ _ := hQ
    _ ≤ 2 ^ (1 * (K + L)) * ((2 ^ (13 * (K + L)) * 2 ^ (cK * (K + L))) * 2 ^ (Z * (K + L))) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.mul_le_mul h2 hK) (hN.trans hN'))
    _ = 2 ^ (eQ l F.filterErrDeg * (K + L)) := by
        rw [← pow_add, ← pow_add, ← pow_add]; congr 1; unfold eQ; rw [← hZ]; ring

/-- **`ℓ ≤ (eQ + 2)(k+L)`** at a SYM call (`ℓ = max(1, 2kh, ⌈log₂Q⌉)`). -/
theorem ell_le {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell ≤
      (eQ l F.filterErrDeg + 2) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) := by
  have hQ := symCount_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hc := Nat.clog_le_of_le_pow hQ
  have hkh := kh_two l F kclk coef A a ha hs
  have hL1 := one_le_L n
  show Sampler.ellFor _ _ ≤ _
  unfold Sampler.ellFor
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hc
  rw [← hKd] at hkh
  rw [← hLd] at hL1
  rw [← hKd, ← hLd]
  have e : (eQ l F.filterErrDeg + 2) * (K + L) = eQ l F.filterErrDeg * (K + L) + 2 * (K + L) := by ring
  rw [e]
  apply max_le (by omega) (max_le (by omega) (by omega))

end Call

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

end
