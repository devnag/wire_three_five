import Proof.Wire_3_5.Primitive.Writers.ThrSide7

/-! # c4 THR block, piece 6 part 8: `hpre` and `CoefFit` at a THR call

The THR twin of the SymHp1–3 and SymOcc4: the request's `h·Q'·d ≤ pr` (**`hqd_thr`**, at the THR degree
`d_D(⌊√(B_T L)⌋ + L²)`), `N^{16}·2^{8ℓ}·2^{Q'} ≤ 2^{pr}` (**`coef_thr`**), the printer's budget within the rectangle
(**`occ_thr`**, under the THR printer floor `occCDT ≤ C_D`: the linear part through `C_D(k+L) ≤ Ψ` and
`C_D·L² ≤ Ψ`, the quadratic part through the THR load `C_D²(k+L)²(⌊√(B_T L)⌋ + L²) ≤ Ψ`), and hence alg:compiler's
precondition at every THR child prefix (**`hpre_thr`**, `pre_of`), with the pool's `CoefFit` (**`thrHcf`**).

* `ThrHpreC`, `hqd_thr`, `coef_thr`, `occCDT`, `occ_thr`, **`hpre_thr`**, **`thrHcf`**.

Paper quantity of the main type: alg:compiler's precondition at a THR call (P3:1882-1900). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC symBud symBud_le cDa n2_le_L one_le_L kh_two
  pow_mono_mul kL_mul_le L2_mul_le two_dRow_ge occ_num pow_N_le cr_le_k)

/-- **The THR constants' constraints for the precondition** (the literals and `f_e` alone). -/
structure ThrHpreC (l : Literals) (fe : ℕ) (alg : RepairRepresentation.DecompositionAlgorithm) (c : SymC) : Prop where
  dQ1 : 1 ≤ c.dQ
  dH : alg.coefficient * 4 ^ alg.degree + 2 ≤ c.dH
  eH : 26 * alg.degree + 1 ≤ c.eH
  dP1 : c.dH * c.dQ * c.dD * 2 ^ (50 + CallIndexR.capZR l) ≤ c.dP
  eP1 : c.eH + 50 + CallIndexR.capZR l ≤ c.eP
  dP2 : 2 * (24 + 8 * eQT l fe + c.dQ) ≤ c.dP
  eP2 : 1 ≤ c.eP
  dD : dDT l fe ≤ c.dD

section Gate
variable (l : Literals) (F : GateFree l)

/-- `⌊√(B_T L)⌋ + L² ≤ 2^{49+Z}(n+1)^{49+Z}` at a THR call (`c_r ≤ k/4 ≤ n`). -/
theorem sqrtCapT_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2)) +
        Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2) ≤
      2 ^ (49 + CallIndexR.capZR l) * (n + 1) ^ (49 + CallIndexR.capZR l) := by
  have hc : ((gate0 l F).budget kclk coef A a ha).capOf .thr n ≤ CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l :=
    CallIndexR.cap_leR l F.cr .thr n
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ n := hcall.2.2.2.2.2.2.kq
  have hcr := cr_le_k l F kclk coef A a ha hs
  have hsq := Nat.sqrt_le_self (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2))
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
  obtain ⟨C, hCd⟩ : ∃ C, C = ((gate0 l F).budget kclk coef A a ha).capOf .thr n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hCd] at hc hsq ⊢
  rw [← hLd] at hsq hL ⊢
  have h3 : C * L ≤ 2 ^ (48 + Z) * (n + 1) ^ (49 + Z) := by
    calc C * L ≤ (CallIndexR.capK F.cr * (n + 2) ^ Z) * (n + 1) := Nat.mul_le_mul hc hL
      _ ≤ ((2 ^ 48 * (n + 1) ^ 48) * (2 ^ Z * (n + 1) ^ Z)) * (n + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2)
      _ = _ := by rw [pow_add, show 49 + Z = 48 + Z + 1 by ring, pow_add, pow_succ]; ring
  have h4 : L * L ≤ (n + 1) * (n + 1) := Nat.mul_le_mul hL hL
  have h5 : (n + 1) * (n + 1) ≤ 2 ^ (48 + Z) * (n + 1) ^ (49 + Z) := by
    have h6 : (n + 1) * (n + 1) = (n + 1) ^ 2 := by ring
    rw [h6]
    have h7 : (n + 1) ^ 2 ≤ (n + 1) ^ (49 + Z) := Nat.pow_le_pow_right (by omega) (by omega)
    have h8 : 1 ≤ 2 ^ (48 + Z) := Nat.one_le_two_pow
    exact h7.trans (Nat.le_mul_of_pos_left _ h8)
  have e : 2 ^ (49 + Z) * (n + 1) ^ (49 + Z) = 2 ^ (48 + Z) * (n + 1) ^ (49 + Z) + 2 ^ (48 + Z) * (n + 1) ^ (49 + Z) := by
    rw [show 49 + Z = (48 + Z) + 1 by ring, pow_succ]; ring
  rw [e]
  omega

/-- **`h·Q'·d ≤ pr`** at a THR call. -/
theorem hqd_thr (c : SymC) (hdP : c.dH * c.dQ * c.dD * 2 ^ (50 + CallIndexR.capZR l) ≤ c.dP)
    (heP : c.eH + 50 + CallIndexR.capZR l ≤ c.eP) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 *
        (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 *
        thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) ≤
      (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 := by
  have hQ := Qp_eq_thr l F c kclk coef A a ha Cs carriers hs
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ n := hcall.2.2.2.2.2.2.kq
  have hL : Nat.clog 2 (n + 2) ≤ n + 1 := Nat.clog_le_of_le_pow (by
    have := Nat.lt_two_pow_self (n := n + 1)
    rw [pow_succ] at this ⊢; omega)
  have hkL : ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) ≤ 2 * (n + 1) := by omega
  have hsc := sqrtCapT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  rw [hQ]
  show c.dH * (n + 1) ^ c.eH * (c.dQ * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) *
      (c.dD * (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2)) +
        Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) ≤ c.dP * (n + 1) ^ c.eP
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = CallIndexR.capZR l := ⟨_, rfl⟩
  rw [← hZ] at hdP heP hsc
  obtain ⟨X, hX⟩ : ∃ X, X = ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2)) +
      Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hX] at hkL ⊢
  rw [← hY] at hsc
  have eY : c.dD * (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2)) +
      Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) = c.dD * Y := by rw [hY]
  rw [eY]
  have hp : (n + 1) ^ c.eH * (n + 1) * (n + 1) ^ (49 + Z) ≤ (n + 1) ^ c.eP := by
    rw [← pow_succ, ← pow_add]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  calc c.dH * (n + 1) ^ c.eH * (c.dQ * X) * (c.dD * Y)
      ≤ c.dH * (n + 1) ^ c.eH * (c.dQ * (2 * (n + 1))) * (c.dD * (2 ^ (49 + Z) * (n + 1) ^ (49 + Z))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hkL)) (Nat.mul_le_mul_left _ hsc)
    _ = c.dH * c.dQ * c.dD * (2 * 2 ^ (49 + Z)) * ((n + 1) ^ c.eH * (n + 1) * (n + 1) ^ (49 + Z)) := by ring
    _ = c.dH * c.dQ * c.dD * 2 ^ (50 + Z) * ((n + 1) ^ c.eH * (n + 1) * (n + 1) ^ (49 + Z)) := by
        rw [show 50 + Z = (49 + Z) + 1 by ring, pow_succ]; ring
    _ ≤ c.dP * (n + 1) ^ c.eP := Nat.mul_le_mul hdP hp

/-- **`N^{16}·2^{8ℓ}·2^{Q'} ≤ 2^{pr}`** at a THR call. -/
theorem coef_thr (c : SymC) (hdP : 2 * (24 + 8 * eQT l F.filterErrDeg + c.dQ) ≤ c.dP) (heP : 1 ≤ c.eP)
    (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).N ^ 16 *
        2 ^ (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) *
        2 ^ (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 ≤
      2 ^ (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 := by
  have hQ := Qp_eq_thr l F c kclk coef A a ha Cs carriers hs
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ n := hcall.2.2.2.2.2.2.kq
  have hL : Nat.clog 2 (n + 2) ≤ n + 1 := Nat.clog_le_of_le_pow (by
    have := Nat.lt_two_pow_self (n := n + 1)
    rw [pow_succ] at this ⊢; omega)
  have hkL : ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) ≤ 2 * (n + 1) := by omega
  have hl := thrEll_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hN : (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).N ^ 16 =
      2 ^ (8 * ((gate0 l F).budget kclk coef A a ha).kOf n) := by
    show (2 ^ SeedFix.callKh _) ^ 16 = _
    rw [← pow_mul]; congr 1; omega
  rw [hN, hQ, ← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  show _ ≤ c.dP * (n + 1) ^ c.eP
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hkL hl ⊢
  have h1 : (n + 1) ≤ (n + 1) ^ c.eP := Nat.le_self_pow (by omega) _
  have h2 : 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell ≤
      8 * ((eQT l F.filterErrDeg + 2) * (K + L)) := Nat.mul_le_mul_left _ hl
  have h3 : (24 + 8 * eQT l F.filterErrDeg + c.dQ) * (K + L) ≤ (24 + 8 * eQT l F.filterErrDeg + c.dQ) * (2 * (n + 1)) :=
    Nat.mul_le_mul_left _ hkL
  have h4 : (2 * (24 + 8 * eQT l F.filterErrDeg + c.dQ)) * (n + 1) ≤ c.dP * (n + 1) ^ c.eP :=
    Nat.mul_le_mul hdP h1
  have e1 : (24 + 8 * eQT l F.filterErrDeg + c.dQ) * (K + L) = 24 * (K + L) + 8 * (eQT l F.filterErrDeg * (K + L)) +
      c.dQ * (K + L) := by ring
  have e2 : 8 * ((eQT l F.filterErrDeg + 2) * (K + L)) = 8 * (eQT l F.filterErrDeg * (K + L)) + 16 * (K + L) := by ring
  have e3 : (24 + 8 * eQT l F.filterErrDeg + c.dQ) * (2 * (n + 1)) =
      (2 * (24 + 8 * eQT l F.filterErrDeg + c.dQ)) * (n + 1) := by ring
  omega

/-- **The THR printer's load floor** (fixed before `F`: the algorithm is the literals'). -/
def occCDT (a : RepairRepresentation.DecompositionAlgorithm) (c : SymC) (A1 cd : ℕ) : ℕ :=
  160 * (A1 + 1392 * cd + 16 + 16 * cd + c.dQ + 1) + 160 * (c.dQ * c.dD * cDa a) + 2

/-- **The printer's budget at the THR child request of every prefix** under the THR printer floor. -/
theorem occ_thr (c : SymC)
    (hCD : occCDT (gate0 l F).alg c (A1T l F.filterErrDeg) (10 * CallIndex.algX l + 32) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (p' : List Bool) :
    (2 * (PrimT.C4Child.chR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3)
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4)
      (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs))
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0)
      (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1)
      (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) p').occBound
        (gate0 l F).alg) *
    (2 * (PrimT.C4Child.chR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3)
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4)
      (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs))
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0)
      (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1)
      (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) p').occBound
        (gate0 l F).alg) ≤
      SourceInterfaces.rectangularInnerDimension (2 ^ PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs)) := by
  have hm := m_le_thr l F c kclk coef A a ha ha' Cs carriers translation hcall hs
  have hQ := Qp_eq_thr l F c kclk coef A a ha Cs carriers hs
  have hV := lenV_thr l F kclk coef A a ha ha' Cs carriers translation hcall hs p'.length (SeedFix.listNum p')
  have hD := thrD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
    ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3)
    ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
  have hfits := hcall.2.2.2.2.2.2.pre
  have hkL := kL_mul_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
    (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hLL := L2_mul_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
    (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hsy := loadThr_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
    (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hdr := two_dRow_ge ((callInputs l F kclk coef A a ha).starParams n hs)
  have hL1 := one_le_L n
  generalize Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs = nT at hV ⊢
  refine FinalPass.SampShape.occ_of (gate0 l F).alg _
    (A1T l F.filterErrDeg * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) +
      1392 * (10 * CallIndex.algX l + 32) * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)))
    (((gate0 l F).budget kclk coef A a ha).kOf n + cDa (gate0 l F).alg * Nat.clog 2 (n + 2)) hV hD ?_
  have hψ : ((gate0 l F).budget kclk coef A a ha).psiOf n = loadPsi F.CD (((gate0 l F).budget kclk coef A a ha).kOf n)
      (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n)
      (((gate0 l F).budget kclk coef A a ha).capOf .sym n) := rfl
  rw [← hψ] at hkL hLL hsy
  have hcp : 1 ≤ (gate0 l F).E.cpsi := hcpsi
  have hn : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤ n := by
    have : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤
        (gate0 l F).E.cpsi * ((gate0 l F).budget kclk coef A a ha).psiOf n := Nat.le_mul_of_pos_left _ hcp
    exact this.trans (le_trans (Nat.le_add_right _ _) hfits)
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  obtain ⟨ψ, hψd⟩ : ∃ ψ, ψ = ((gate0 l F).budget kclk coef A a ha).psiOf n := ⟨_, rfl⟩
  obtain ⟨S, hSd⟩ : ∃ S, S = Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2)) :=
    ⟨_, rfl⟩
  obtain ⟨m4, hm4d⟩ : ∃ m, m = (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg
    Cs carriers hs) 4 := ⟨_, rfl⟩
  obtain ⟨dR, hdRd⟩ : ∃ d, d = PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  obtain ⟨cd, hcd⟩ : ∃ c, c = 10 * CallIndex.algX l + 32 := ⟨_, rfl⟩
  have hdr' : n - K ≤ 2 * dR := by rw [hKd, hdRd]; exact hdr
  rw [← hKd, ← hLd] at hm hkL hsy hQ
  rw [← hLd] at hLL
  rw [← hψd] at hkL hLL hsy hn
  rw [← hLd] at hSd
  rw [← hSd] at hsy
  rw [← hm4d] at hm
  rw [← hcd] at hm hCD
  have hCD1 : 2 ≤ F.CD := by unfold occCDT at hCD; omega
  have hC1 : 160 * (A1T l F.filterErrDeg + 1392 * cd + 16 + 16 * cd + c.dQ + 1) ≤ F.CD := by
    unfold occCDT at hCD; omega
  have hC2 : 160 * (c.dQ * c.dD * cDa (gate0 l F).alg) ≤ F.CD * F.CD := by
    unfold occCDT at hCD
    have : F.CD ≤ F.CD * F.CD := Nat.le_mul_self _
    omega
  have hcDa : 1 ≤ cDa (gate0 l F).alg := by unfold cDa; omega
  -- the linear part
  have hA : F.CD * (A1T l F.filterErrDeg * (K + L) + 1392 * cd * (L * L) + m4 + c.dQ * (K + L) + 1) ≤
      (A1T l F.filterErrDeg + 1392 * cd + 16 + 16 * cd + c.dQ + 1) * ψ := by
    have h1 : A1T l F.filterErrDeg * (K + L) + m4 + c.dQ * (K + L) + 1 ≤
        (A1T l F.filterErrDeg + 16 + 16 * cd + c.dQ + 1) * (K + L) := by
      have e : (A1T l F.filterErrDeg + 16 + 16 * cd + c.dQ + 1) * (K + L) = A1T l F.filterErrDeg * (K + L) +
          (16 + 16 * cd) * (K + L) + c.dQ * (K + L) + (K + L) := by ring
      omega
    have h2 : F.CD * (A1T l F.filterErrDeg * (K + L) + 1392 * cd * (L * L) + m4 + c.dQ * (K + L) + 1) ≤
        (A1T l F.filterErrDeg + 16 + 16 * cd + c.dQ + 1) * (F.CD * (K + L)) + 1392 * cd * (F.CD * (L * L)) := by
      have := Nat.mul_le_mul_left F.CD h1
      have e1 : F.CD * (A1T l F.filterErrDeg * (K + L) + 1392 * cd * (L * L) + m4 + c.dQ * (K + L) + 1) =
          F.CD * (A1T l F.filterErrDeg * (K + L) + m4 + c.dQ * (K + L) + 1) + 1392 * cd * (F.CD * (L * L)) := by ring
      have e2 : F.CD * ((A1T l F.filterErrDeg + 16 + 16 * cd + c.dQ + 1) * (K + L)) =
          (A1T l F.filterErrDeg + 16 + 16 * cd + c.dQ + 1) * (F.CD * (K + L)) := by ring
      omega
    have h3 : (A1T l F.filterErrDeg + 16 + 16 * cd + c.dQ + 1) * (F.CD * (K + L)) ≤
        (A1T l F.filterErrDeg + 16 + 16 * cd + c.dQ + 1) * ψ := Nat.mul_le_mul_left _ hkL
    have h4 : 1392 * cd * (F.CD * (L * L)) ≤ 1392 * cd * ψ := Nat.mul_le_mul_left _ hLL
    have e3 : (A1T l F.filterErrDeg + 1392 * cd + 16 + 16 * cd + c.dQ + 1) * ψ =
        (A1T l F.filterErrDeg + 16 + 16 * cd + c.dQ + 1) * ψ + 1392 * cd * ψ := by ring
    omega
  -- the quadratic part
  have hB : F.CD * F.CD * (c.dQ * (K + L) * (c.dD * (S + L * L)) * (K + cDa (gate0 l F).alg * L)) ≤
      (c.dQ * c.dD * cDa (gate0 l F).alg) * ψ := by
    have h1 : K + cDa (gate0 l F).alg * L ≤ cDa (gate0 l F).alg * (K + L) := by
      have := Nat.mul_le_mul_right K hcDa
      have e : cDa (gate0 l F).alg * (K + L) = cDa (gate0 l F).alg * K + cDa (gate0 l F).alg * L := by ring
      omega
    calc F.CD * F.CD * (c.dQ * (K + L) * (c.dD * (S + L * L)) * (K + cDa (gate0 l F).alg * L))
        ≤ F.CD * F.CD * (c.dQ * (K + L) * (c.dD * (S + L * L)) * (cDa (gate0 l F).alg * (K + L))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = (c.dQ * c.dD * cDa (gate0 l F).alg) * (F.CD * F.CD * ((K + L) * (K + L) * (S + L * L))) := by ring
      _ ≤ (c.dQ * c.dD * cDa (gate0 l F).alg) * ψ := Nat.mul_le_mul_left _ hsy
  have hk2 : 2 * K ≤ ψ := by
    have : 2 * (K + L) ≤ F.CD * (K + L) := Nat.mul_le_mul_right _ hCD1
    omega
  have key := occ_num ψ n K dR F.CD (A1T l F.filterErrDeg * (K + L) + 1392 * cd * (L * L) + m4 + c.dQ * (K + L))
    (c.dQ * (K + L) * (c.dD * (S + L * L)) * (K + cDa (gate0 l F).alg * L))
    (A1T l F.filterErrDeg + 1392 * cd + 16 + 16 * cd + c.dQ + 1)
    (c.dQ * c.dD * cDa (gate0 l F).alg) (by omega) hA hB hC1 hC2 hn hk2 hdr'
  rw [← hQ] at key
  rw [hSd, hKd, hLd, hm4d, hdRd, hcd] at key
  exact key

/-- **The THR pool fits at `h = d_H(n+1)^{e_H}`** at a THR call (`poolFits_of` at the THR pool). -/
theorem fits_thr (c : SymC) (hdH : (gate0 l F).alg.coefficient * 4 ^ (gate0 l F).alg.degree + 2 ≤ c.dH)
    (heH : 26 * (gate0 l F).alg.degree + 1 ≤ c.eH) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Q psi : ℕ) :
    Pool.CoefFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
        (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) Q psi) ∧
      Req.PNFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
        (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) Q psi) ∧
      Req.DenseFit ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3)
        (Pool.densePool (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
          (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) Q psi).gates
          (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
          (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))) := by
  have hcar : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hb := symBud_le (gate0 l F).alg n
  refine thr_fits_of (gate0 l F).alg ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers hcar hd _ Q psi ?_
  show symBud (gate0 l F).alg n + n + 2 ≤ c.dH * (n + 1) ^ c.eH
  exact hb.trans (Nat.mul_le_mul hdH (Nat.pow_le_pow_right (by omega) heH))

/-- **`C3Req.Pre` at the THR child request of every prefix** (ThrEAt3's `hpre`). -/
theorem hpre_thr (c : SymC) (hc : ThrHpreC l F.filterErrDeg (gate0 l F).alg c)
    (hCD : occCDT (gate0 l F).alg c (A1T l F.filterErrDeg) (10 * CallIndex.algX l + 32) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (p' : List Bool) :
    (PrimT.C4Child.chR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4)
      (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0)
      (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1)
      (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) p').Pre (gate0 l F).alg := by
  have hQ := Qp_eq_thr l F c kclk coef A a ha Cs carriers hs
  have hfits := fits_thr l F c hc.dH hc.eH kclk coef A a ha ha' Cs carriers translation hcall hs ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
  have hocc := occ_thr l F c hCD hcpsi kclk coef A a ha ha' Cs carriers translation hcall hs p'
  have hDg : thrDg l F kclk coef A a ha Cs carriers translation hs ≤ thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) := by
    have h1 := thrDg_lin l F kclk coef A a ha ha' Cs carriers translation hcall hs
    show _ ≤ c.dD * (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2)) +
        Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))
    exact h1.trans (Nat.mul_le_mul_right _ hc.dD)
  have hL1 := one_le_L n
  generalize Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs = nT at hocc ⊢
  refine FinalPass.SampShape.pre_of (gate0 l F).alg _ _ nT (carriers.length + 1)
    (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) p'
    (thrF l F kclk coef A a ha Cs carriers hs) (thrDg l F kclk coef A a ha Cs carriers translation hs) _ _
    (thrBatchFacts l F kclk coef A a ha Cs carriers translation hs)
    (FinalPass.C3Geo.poolReq_pre _ _ _ _ _ _) ?_ ?_ (thr_hmf l F c kclk coef A a ha Cs carriers hs) hDg ?_
    hfits.2.1 hfits.2.2
    (hqd_thr l F c hc.dP1 hc.eP1 kclk coef A a ha ha' Cs carriers translation hcall hs)
    (coef_thr l F c hc.dP2 hc.eP2 kclk coef A a ha ha' Cs carriers translation hcall hs)
    (FinalPass.C3Geo.width_le_dRow _) (PrimT.C4Geo.cols_length _) (FinalPass.C3Geo.cols_lt _) hocc
  · show 1 ≤ max (mOf (thrK2 c).k (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 8
    exact le_trans (by norm_num) (le_max_right _ _)
  · show 1 ≤ ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2)
    rw [hQ]
    exact Nat.mul_le_mul hc.dQ1 (show 1 ≤ ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) by omega)
  · show _ ≤ (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length *
      ((Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).map PrimT.C4Geo.suppG).length
    rw [List.length_map]

/-- **The THR pool's coefficients within `h` bits** at a THR call (ThrEAt3's `CoefFit`). -/
theorem thrHcf (c : SymC) (hc : ThrHpreC l F.filterErrDeg (gate0 l F).alg c) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    Pool.CoefFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0) :=
  (fits_thr l F c hc.dH hc.eH kclk coef A a ha ha' Cs carriers translation hcall hs _ 0).1

/-- **`1 ≤ h`** at a THR call. -/
theorem thrH1 (c : SymC) (hc : ThrHpreC l F.filterErrDeg (gate0 l F).alg c) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    1 ≤ ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) := by
  show 1 ≤ c.dH * (n + 1) ^ c.eH
  have h2 : 2 ≤ c.dH := le_trans (Nat.le_add_left 2 _) hc.dH
  exact Nat.mul_pos (by omega) (by positivity)

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
