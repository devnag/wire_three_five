import Lean
import Proof.Wire_3_5.Primitive.Writers.ThrSide6Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrSide1
import Proof.Wire_3_5.Primitive.Writers.ThrSide2
import Proof.Wire_3_5.Primitive.Writers.ThrSide3
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 THR block, piece 6 part 7: the THR child request's precondition (`hpre`, `CoefFit`)

The THR twin of the SymBF, SymHp1–3, SymOcc3–4 (P3:1882-1900, alg:compiler's precondition; P3:2477-2496 and
3011-3016 the THR batch; P3:3094-3107 the THR load): at a THR call, the THR batch meets `SampShape.BatchFacts` with
`f r = 1` (carrier rows) or `2τ₀` (the RADIX row) and `8·Σf = m`; the request's `h·Q'·d ≤ pr`,
`N^{16}·2^{8ℓ}·2^{Q'} ≤ 2^{pr}`, the pool's fits at `h = d_H(n+1)^{e_H}`, and the printer's budget `occBound` within
the rectangle (the child expression's `≤ 2^{A₁(k+L) + 1392c_d L²}` terms, the dense pool's `≤ 2^{k + c_{Da}L}`
children) under the THR printer floor `occCDT ≤ C_D`; hence `hpre` at every child prefix (the `pre_of`).

* `Qp_eq_thr`, `dig_pos`, `m_eq_thr`, `m_le_thr`, `thrF`, **`thr_hmf`**, **`thrBatchFacts`**, `thrT_le2`, `A1T`,
  **`lenV_thr`**, **`hqd_thr`**, **`coef_thr`**, `occCDT`, **`occ_thr`**, **`hpre_thr`**, **`thrHcf`**.

Paper quantity of the main type: alg:compiler's precondition at a THR call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC symBud symBud_le cDa n2_le_L one_le_L kh_two
  pow_mono_mul sum_split kL_mul_le two_dRow_ge occ_num pow_N_le)

section Gate
variable (l : Literals) (F : GateFree l)

/-- `Q' = d_Q(k+L)` at a THR call. -/
theorem Qp_eq_thr (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 =
      c.dQ * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) := by
  have hkh := kh_two l F kclk coef A a ha hs
  show c.dQ * (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) +
    SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + Nat.clog 2 (n + 2)) = _
  have e0 : SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) +
      SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + Nat.clog 2 (n + 2) =
      ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) := by omega
  rw [e0]

/-- The digit count is positive (the cutoff is at least `563`). -/
theorem dig_pos (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    1 ≤ thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) := by
  have h := SupplierPrime.canonicalPrimeCutoff_ge_563
    (SupplierPrime.familyMagnitudeExponent (thrRealize ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg))
    (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
  unfold thrDigits
  exact Nat.clog_pos (by norm_num) (by unfold thrCutoff; omega)

/-- `m = 8·|carriers| + 16·τ₀` at a THR call. -/
theorem m_eq_thr (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4 =
      8 * carriers.length + 16 * thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
        (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) := by
  have hd := dig_pos l F kclk coef A a ha Cs hs
  show max (mOf (thrK2 c).k (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 8 = _
  unfold mOf
  show max (8 * carriers.length + 0 * (a' * W (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs
    carriers hs)) + 0 * W (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) + 0 * a' +
    16 * thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) + 0) 8 = _
  simp only [Nat.zero_mul, Nat.add_zero]
  exact max_eq_left (by omega)

/-- `m ≤ (16 + 16c_d)(k+L)` at a THR call (`c_d = 10X + 32`). -/
theorem m_le_thr (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4 ≤
      (16 + 16 * (10 * CallIndex.algX l + 32)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hdig := dig_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL1 := one_le_L n
  rw [m_eq_thr l F c kclk coef A a ha Cs carriers hs]
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd] at hdig hL1
  rw [← hKd, ← hLd]
  have h1 : 16 * (10 * CallIndex.algX l + 32) * L ≤ 16 * (10 * CallIndex.algX l + 32) * (K + L) :=
    Nat.mul_le_mul_left _ (by omega)
  have e : (16 + 16 * (10 * CallIndex.algX l + 32)) * (K + L) = 16 * (K + L) + 16 * (10 * CallIndex.algX l + 32) * (K + L) := by
    ring
  have e2 : 16 * ((10 * CallIndex.algX l + 32) * L) = 16 * (10 * CallIndex.algX l + 32) * L := by ring
  omega

/-- The THR rows' factor counts by row position (the `thr_rows_factors`). -/
noncomputable def thrF (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : ℕ → ℕ :=
  fun r => if r < carriers.length then 1 else 2 * thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs
    (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)

/-- **The child's factor count is `m`** at a THR call. -/
theorem thr_hmf (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    8 * ((List.range (carriers.length + 1)).map (thrF l F kclk coef A a ha Cs carriers hs)).sum =
      (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4 := by
  rw [m_eq_thr l F c kclk coef A a ha Cs carriers hs]
  unfold thrF
  rw [sum_split]
  ring

/-- **The THR batch's facts.** -/
theorem thrBatchFacts (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    FinalPass.SampShape.BatchFacts (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
      (carriers.length + 1) (thrF l F kclk coef A a ha Cs carriers hs) (thrDg l F kclk coef A a ha Cs carriers translation hs)
      ((PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length *
        (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length)
      ((((Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M + 1) ^ 2) ^
        thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) := by
  have hfl : (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length =
      4 * (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) *
        2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) := by
    simp [PrimT.C4Geo.flips]
  refine ⟨BShape.thr_rows_factors (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation,
    fun V hV t ht p hp => ?_, fun V hV t ht => Or.inl (BShape.thr_coef_one (gate0 l F).alg
      (callInputs l F kclk coef A a ha) hs Cs carriers translation V hV t ht),
    BShape.thr_row_terms_le (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation⟩
  rw [hfl]
  exact BShape.thr_factors_ok (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation V hV t ht p hp

/-- **The THR rows' term bound below `2^{58c_d L²}`.** -/
theorem thrT_le2 (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (((Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M + 1) ^ 2) ^
        thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ≤
      2 ^ (58 * (10 * CallIndex.algX l + 32) * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) := by
  have hM := occ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hdig := dig_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hN := pow_N_le n 26
  have hL1 := one_le_L n
  have h26 : (n + 1) ^ 26 ≤ 2 ^ (26 * Nat.clog 2 (n + 2)) := (Nat.pow_le_pow_left (by omega) 26).trans hN
  have h0 := Nat.one_le_two_pow (n := 26 * Nat.clog 2 (n + 2))
  have hM1 : (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M + 1 ≤
      2 ^ (26 * Nat.clog 2 (n + 2) + 3) := by
    rw [thrCallD_M, pow_add]; omega
  have h2 := pow_mono_mul 2 hM1
  have h3 := pow_mono_mul (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
    (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) h2
  refine h3.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd] at hdig hL1 ⊢
  obtain ⟨d, hdd⟩ : ∃ d, d = thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
    (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) := ⟨_, rfl⟩
  rw [← hdd] at hdig ⊢
  have h4 : d * (2 * (26 * L + 3)) ≤ ((10 * CallIndex.algX l + 32) * L) * (58 * L) :=
    Nat.mul_le_mul hdig (by omega)
  have e : ((10 * CallIndex.algX l + 32) * L) * (58 * L) = 58 * (10 * CallIndex.algX l + 32) * (L * L) := by ring
  omega

/-- The THR term-count exponent's linear coefficient. -/
noncomputable def A1T (l : Literals) (fe : ℕ) : ℕ := eNT l fe + 4 + 8 * (eQT l fe + 2) + 8

/-- **The THR child expression has `≤ 2^{A₁(k+L) + 1392c_d L²}` terms** at a THR call. -/
theorem lenV_thr (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (plen pre : ℕ) :
    (SeedFix.sampTerms (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1)
      (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) plen pre).length ≤
      2 ^ (A1T l F.filterErrDeg * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) +
        1392 * (10 * CallIndex.algX l + 32) * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have h0 := FinalPass.SampShape.length_sampTerms_leT (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1)
    (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) plen pre _
    (BShape.thr_row_terms_le (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
  have hT := thrT_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hNT := thrNT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hl := thrEll_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hL1 := one_le_L n
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hNT hl ⊢
  rw [← hLd] at hT hL1
  rw [← hKd] at hkh
  obtain ⟨cd, hcd⟩ : ∃ c, c = 10 * CallIndex.algX l + 32 := ⟨_, rfl⟩
  rw [← hcd] at hT ⊢
  have hN8 : (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).N ^ 8 ≤ 2 ^ (4 * (K + L)) := by
    show (2 ^ SeedFix.callKh _) ^ 8 ≤ _
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hl8 : (2 ^ (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) ^ 8 ≤
      2 ^ (8 * (eQT l F.filterErrDeg + 2) * (K + L)) := by
    rw [← pow_mul]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := Nat.mul_le_mul_right 8 hl
    have e : 8 * (eQT l F.filterErrDeg + 2) * (K + L) = (eQT l F.filterErrDeg + 2) * (K + L) * 8 := by ring
    omega
  have h28 : 2 ^ 8 ≤ 2 ^ (8 * (K + L)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hT8 : ((((Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M + 1) ^ 2) ^
      thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
        (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) ^ (8 * (carriers.length + 1)) ≤
      2 ^ (1392 * cd * (L * L)) := by
    calc _ ≤ (2 ^ (58 * cd * (L * L))) ^ (8 * (carriers.length + 1)) := Nat.pow_le_pow_left hT _
      _ = 2 ^ (58 * cd * (L * L) * (8 * (carriers.length + 1))) := by rw [← pow_mul]
      _ ≤ 2 ^ (1392 * cd * (L * L)) := Nat.pow_le_pow_right (by norm_num) (by
          have := Nat.mul_le_mul_left (58 * cd * (L * L)) (show 8 * (carriers.length + 1) ≤ 24 by omega)
          have e : 1392 * cd * (L * L) = 58 * cd * (L * L) * 24 := by ring
          omega)
  refine h0.trans ?_
  calc _ ≤ 2 ^ (eNT l F.filterErrDeg * (K + L)) * (2 ^ (4 * (K + L)) *
        (2 ^ (8 * (eQT l F.filterErrDeg + 2) * (K + L)) * (2 ^ (8 * (K + L)) * 2 ^ (1392 * cd * (L * L))))) :=
        Nat.mul_le_mul hNT (Nat.mul_le_mul hN8 (Nat.mul_le_mul hl8 (Nat.mul_le_mul h28 hT8)))
    _ = 2 ^ (A1T l F.filterErrDeg * (K + L) + 1392 * cd * (L * L)) := by
        rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; unfold A1T; ring

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide

end
