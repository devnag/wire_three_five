import Lean
import Proof.Wire_3_5.FinalPass.SymBuildBase
import Proof.Wire_3_5.Primitive.Writers.ThrCap4Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 THR block, piece 6 part 1: the THR call's `n_T`, `Q`, `ℓ` below `2^{e(k+L)}` (twin of the SymSz2)

P3:2987-2988, 3154-3162 (`samp:q` at a THR call), P3:2543-2558 (`n_T = |GapSeed|·|𝒢|·Σ_{p ≤ cutoff} p`), P3:1189
(`k = r⌊log₂(n/r+1)⌋`, `4c_r ≤ k`): at a THR call of the gate, `n_T ≤ 2^{e_N(k+L)}`, `Q ≤ 2^{e_Q(k+L)}` and
`ℓ ≤ (e_Q + 2)(k+L)`, the exponents depending on `l` and `f_e` only (the THR index's `gapK c_r ≤ symKI c_r ≤
2^{c_K(k+L)}`, CallIndex's `thrEq_le`, `cut_le`).

* `eNT`, `eQT`; **`thrNT_le`**, **`thrCount_le`**, **`thrEll_le`**.

Paper quantities of the main types: the THR call's `n_T`, `Q`, `ℓ` against `2^{k+L}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (cK pow_N_le one_le_L symKI_kL kh_two)

/-- The exponent of the THR state count. -/
noncomputable def eNT (l : Literals) (fe : ℕ) : ℕ :=
  cK + (CallIndexR.gapZR l fe + (CallIndex.algX l * 4 + (20 * CallIndex.algX l + 65)))

/-- The exponent of the THR count. -/
noncomputable def eQT (l : Literals) (fe : ℕ) : ℕ := 1 + 13 + cK + (CallIndexR.thrZI l fe + 2)

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- `gapK c_r ≤ 2^{c_K(k+L)}` at an on-star length (`flatK ≥ 1`). -/
theorem gapK_kL {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    CallIndexR.gapK F.cr ≤ 2 ^ (cK * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) := by
  have h := symKI_kL l F kclk coef A a ha hs
  have h1 : CallIndexR.gapK F.cr ≤ CallIndexR.symKI F.cr := by
    unfold CallIndexR.symKI
    exact Nat.le_mul_of_pos_right _ (CallIndexR.flatK_pos F.cr)
  exact h1.trans h

/-- **`n_T ≤ 2^{e_N(k+L)}`** at a THR call. -/
theorem thrNT_le {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
      2 ^ (eNT l F.filterErrDeg * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hg := CallIndexR.gapSeed_leR l F kclk coef A a ha .thr n
  have hq := CallIndex.thrEq_le l F kclk coef A a ha n hs ha' Cs hd
  have hc := CallIndex.cut_le l F kclk coef A a ha n hs ha' Cs hd
  set c := thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
    (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) with hcd
  obtain ⟨N, hNd⟩ : ∃ N, N = n + 2 := ⟨_, rfl⟩
  rw [← hNd] at hg hq hc
  have hN : 2 ≤ N := by omega
  have hsig : ThrQ.primeSum c ≤ N ^ (20 * CallIndex.algX l + 65) := by
    rw [← ThrQ.card_primeRows]
    have h := CallIndex.sigma_le c
    have hp : 1 ≤ N ^ (10 * CallIndex.algX l + 32) := Nat.one_le_pow _ _ (by omega)
    have hc1 : c + 1 ≤ N ^ (10 * CallIndex.algX l + 33) := by rw [pow_succ]; nlinarith
    have e : N ^ (20 * CallIndex.algX l + 65) = N ^ (10 * CallIndex.algX l + 33) * N ^ (10 * CallIndex.algX l + 32) := by
      rw [← pow_add]; congr 1; omega
    rw [e]; exact le_trans h (Nat.mul_le_mul hc1 hc)
  have hNT : Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
      CallIndexR.gapK F.cr * N ^ (CallIndexR.gapZR l F.filterErrDeg +
        (CallIndex.algX l * 4 + (20 * CallIndex.algX l + 65))) := by
    rw [Enum.thrNT_eq, ← Filters.card_gapSeed]
    calc _ ≤ (CallIndexR.gapK F.cr * N ^ CallIndexR.gapZR l F.filterErrDeg) *
          (N ^ (CallIndex.algX l * 4) * N ^ (20 * CallIndex.algX l + 65)) :=
          Nat.mul_le_mul hg (Nat.mul_le_mul hq hsig)
      _ = _ := by rw [pow_add, pow_add]; ring
  have hK := gapK_kL l F kclk coef A a ha hs
  have hL1 := one_le_L n
  have hP := pow_N_le n (CallIndexR.gapZR l F.filterErrDeg + (CallIndex.algX l * 4 + (20 * CallIndex.algX l + 65)))
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hK
  rw [← hLd] at hP hL1
  rw [← hNd] at hP
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = CallIndexR.gapZR l F.filterErrDeg + (CallIndex.algX l * 4 + (20 * CallIndex.algX l + 65)) :=
    ⟨_, rfl⟩
  rw [← hZ] at hNT hP
  rw [← hKd, ← hLd]
  have hP' : 2 ^ (Z * L) ≤ 2 ^ (Z * (K + L)) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  calc _ ≤ _ := hNT
    _ ≤ 2 ^ (cK * (K + L)) * 2 ^ (Z * (K + L)) := Nat.mul_le_mul hK (hP.trans hP')
    _ = 2 ^ (eNT l F.filterErrDeg * (K + L)) := by rw [← pow_add, ← Nat.add_mul, hZ]; rfl

/-- **`Q ≤ 2^{e_Q(k+L)}`** at a THR call. -/
theorem thrCount_le {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
      2 ^ (eQT l F.filterErrDeg * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hQ := CallIndexR.thrCount_leR l F kclk coef A a ha n hs ha' Cs hd
  have hx := CallIndexR.kh_exp_le l F kclk coef A a ha n hs
  have hL1 := one_le_L n
  have hK := gapK_kL l F kclk coef A a ha hs
  have hN := pow_N_le n (CallIndexR.thrZI l F.filterErrDeg + 2)
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd] at hx
  rw [← hKd, ← hLd] at hK
  rw [← hLd] at hN hL1
  rw [← hKd, ← hLd]
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = CallIndexR.thrZI l F.filterErrDeg + 2 := ⟨_, rfl⟩
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
    _ = 2 ^ (eQT l F.filterErrDeg * (K + L)) := by
        rw [← pow_add, ← pow_add, ← pow_add]; congr 1; unfold eQT; rw [← hZ]; ring

/-- **`ℓ ≤ (e_Q + 2)(k+L)`** at a THR call (`ℓ = max(1, 2kh, ⌈log₂Q⌉)`). -/
theorem thrEll_le {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell ≤
      (eQT l F.filterErrDeg + 2) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) := by
  have hQ := thrCount_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hc := Nat.clog_le_of_le_pow hQ
  have hkh := kh_two l F kclk coef A a ha hs
  have hL1 := one_le_L n
  show max 1 (max (2 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
    (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤ _
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hc
  rw [← hKd] at hkh
  rw [← hLd] at hL1
  rw [← hKd, ← hLd]
  have e : (eQT l F.filterErrDeg + 2) * (K + L) = eQT l F.filterErrDeg * (K + L) + 2 * (K + L) := by ring
  rw [e]
  apply max_le (by omega) (max_le (by omega) (by omega))

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide

end
