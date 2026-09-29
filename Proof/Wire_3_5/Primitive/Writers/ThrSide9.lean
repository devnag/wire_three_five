import Proof.Wire_3_5.Primitive.Writers.ThrSide8

/-! # c4 THR block, piece 6 part 9: the range and the request's numbers at a THR call

The THR twins of the SymHr and SymCost1-2 (RULING: plain THR twins on the mode-generic cores).
* **`hrange_thr`** (ThrEAt3's exact recovery range): `2^{m−1}·V_p(z) < 2^{Q'}` at `Q' = d_Q(k+L)`, `d_Q ≥ cST + 1`
  (alg:compiler, P3:1886-1890; samp:range, P3:2919-2921), through the generic `sampElim_lt`.
* `sT` (`⌊√(B_T L)⌋ + L² − L`, so that the SYM shape `U = (k+L)²(S+L)` is the THR load's `(k+L)²(⌊√(B_T L)⌋ + L²)`),
  `cmT` (`m ≤ c_m(k+L)`), `add_le_pow_add`, **`fix_numT`** (`fix_num` at `m ≤ c_m(k+L)`: the exponent
  `efOf (c_D + c_m)`), **`occ_numT`** (the occurrence count at `A ≤ 2^{A₁(k+L) + B·L²}`, `m ≤ c_m(k+L)`).
* **`thrFix_le`** (the THR request's fixed fields and displayed parameters below `2^{e_F}`), **`thrOcc_le`** (the
  charged occurrence count at every prefix below `2^{c_O U}`).

Paper quantities of the main types: the exact recovery range and the compiler input's size and `𝒮` at a THR child
request (P3:1886-1906, 3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC cDa one_le_L n2_le_L kh_two pow_mono_mul kL_le_U fix_num
  efOf coOf lt_pow_self' dense_length two_dRow_le n26_le bnOf sampElim_lt)

/-- **The THR range constant** (`d_Q ≥ cST + 1`). -/
noncomputable def cST (l : Literals) (fe : ℕ) : ℕ := 16 * eQT l fe + eNT l fe + 160 * CallIndex.algX l + 600

/-- **The THR load's square-root term, shifted**: `⌊√(B L)⌋ + L² − L`. -/
def sT (B L : ℕ) : ℕ := Nat.sqrt (B * L) + L * L - L

theorem sT_add (B L : ℕ) : sT B L + L = Nat.sqrt (B * L) + L * L := by
  unfold sT
  have := Nat.le_mul_self L
  omega

/-- **The THR factor count's coefficient** (`m ≤ c_m(k+L)`). -/
noncomputable def cmT (l : Literals) : ℕ := 16 + 16 * (10 * CallIndex.algX l + 32)

theorem add_le_pow_add {x y a b : ℕ} (hx : x ≤ 2 ^ a) (hy : y ≤ 2 ^ b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    x + y ≤ 2 ^ (a + b) := by
  have h1 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have h2 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  rw [pow_add]
  generalize 2 ^ a = A at hx h1
  generalize 2 ^ b = B at hy h2
  nlinarith

/-- **The fixed fields and the displayed parameters below `2^{e_F}`** at `m ≤ c_m(k+L)` (`fix_num` at
`m = 0`, plus the factor count at `2^{c_m U}`). -/
theorem fix_numT (K L S n cD cm dQ dD dH eH dP eP Qv Df Dl m h pr w dR cl dg Pex : ℕ)
    (hL1 : 1 ≤ L) (hn : n + 2 ≤ 2 ^ L) (hcD : 1 ≤ cD) (hcm : 1 ≤ cm)
    (hQ : Qv = dQ * (K + L)) (hDf : Df + 1 ≤ 2 ^ (K + cD * L)) (hDl : Dl ≤ 2 ^ (K + 26 * L + 5))
    (hm : m ≤ cm * (K + L)) (hh : h = dH * (n + 1) ^ eH) (hpr : pr = dP * (n + 1) ^ eP)
    (hw : w ≤ n + 1) (hdR : dR ≤ n + 1) (hcl : cl ≤ n + 1) (hdg : dg = dD * (S + L)) (hPex : Pex ≤ Df) :
    Qv + Df + Dl + m + h + pr + w + dR + cl + 1 + (pr + w + Pex + h + Qv + dg + 1) ≤
      2 ^ efOf (cD + cm) dQ dD dH eH dP eP ((K + L) * (K + L) * (S + L)) L := by
  have k0 := fix_num K L S n cD dQ dD dH eH dP eP Qv Df Dl 0 h pr w dR cl dg Pex hL1 hn hcD hQ hDf hDl
    (Nat.zero_le _) hh hpr hw hdR hcl hdg hPex
  have hKU := kL_le_U K L S hL1
  obtain ⟨U, hU⟩ : ∃ U, U = (K + L) * (K + L) * (S + L) := ⟨_, rfl⟩
  rw [← hU] at k0 hKU ⊢
  have tm : m ≤ 2 ^ (cm * U) := by
    have : m ≤ cm * U := hm.trans (Nat.mul_le_mul_left _ hKU)
    exact this.trans (lt_pow_self' _)
  have e : efOf (cD + cm) dQ dD dH eH dP eP U L = efOf cD dQ dD dH eH dP eP U L + cm * U := by unfold efOf; ring
  have h1 : 1 ≤ efOf cD dQ dD dH eH dP eP U L := by unfold efOf; omega
  have h2 : 1 ≤ cm * U := Nat.mul_pos (by omega) (by omega)
  rw [e]
  have := add_le_pow_add k0 tm h1 h2
  omega

/-- **The charged occurrence count below `2^{c_O U}`** at `A ≤ 2^{A₁(k+L) + B·L²}`, `m ≤ c_m(k+L)`, `L² ≤ S + L`. -/
theorem occ_numT (K L S A1c B cm cD dQ dD Vl m Qv Df d : ℕ) (hL1 : 1 ≤ L) (hcD : 1 ≤ cD) (hLL : L * L ≤ S + L)
    (hV : Vl ≤ 2 ^ (A1c * (K + L) + B * (L * L))) (hm : m ≤ cm * (K + L)) (hQ : Qv = dQ * (K + L))
    (hDf : Df + 1 ≤ 2 ^ (K + cD * L)) (hd : d = dD * (S + L)) :
    max 1 Vl * 2 ^ m * (Qv * (Df + 1) ^ (Qv * d)) ≤
      2 ^ (coOf (A1c + B + cm) dQ cD dD * ((K + L) * (K + L) * (S + L))) := by
  obtain ⟨U, hU⟩ : ∃ U, U = (K + L) * (K + L) * (S + L) := ⟨_, rfl⟩
  rw [← hU]
  have hKU : K + L ≤ U := by rw [hU]; exact kL_le_U K L S hL1
  have hLU : L * L ≤ U := by
    rw [hU]
    calc L * L ≤ S + L := hLL
      _ = 1 * 1 * (S + L) := by ring
      _ ≤ (K + L) * (K + L) * (S + L) := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  have h1 : max 1 Vl ≤ 2 ^ (A1c * (K + L) + B * (L * L)) := max_le Nat.one_le_two_pow hV
  have h2 : 2 ^ m ≤ 2 ^ (cm * (K + L)) := Nat.pow_le_pow_right (by norm_num) hm
  have h3 : Qv ≤ 2 ^ (dQ * (K + L)) := by rw [hQ]; exact lt_pow_self' _
  have h4 : (Df + 1) ^ (Qv * d) ≤ 2 ^ ((Qv * d) * (K + cD * L)) := pow_mono_mul _ hDf
  have h5 : (Qv * d) * (K + cD * L) ≤ cD * dQ * dD * U := by
    have a1 : K + cD * L ≤ cD * (K + L) := by
      have := Nat.mul_le_mul_right K hcD
      have e : cD * (K + L) = cD * K + cD * L := by ring
      omega
    rw [hQ, hd, hU]
    calc dQ * (K + L) * (dD * (S + L)) * (K + cD * L) ≤ dQ * (K + L) * (dD * (S + L)) * (cD * (K + L)) :=
          Nat.mul_le_mul_left _ a1
      _ = cD * dQ * dD * ((K + L) * (K + L) * (S + L)) := by ring
  have h6 : A1c * (K + L) + B * (L * L) + cm * (K + L) + dQ * (K + L) ≤ (A1c + B + cm + 400 + dQ) * U := by
    have a1 : A1c * (K + L) ≤ A1c * U := Nat.mul_le_mul_left _ hKU
    have a2 : B * (L * L) ≤ B * U := Nat.mul_le_mul_left _ hLU
    have a3 : cm * (K + L) ≤ cm * U := Nat.mul_le_mul_left _ hKU
    have a4 : dQ * (K + L) ≤ dQ * U := Nat.mul_le_mul_left _ hKU
    have e : (A1c + B + cm + 400 + dQ) * U = A1c * U + B * U + cm * U + 400 * U + dQ * U := by ring
    omega
  have hE : 2 ^ (A1c * (K + L) + B * (L * L)) * 2 ^ (cm * (K + L)) * (2 ^ (dQ * (K + L)) * 2 ^ ((Qv * d) * (K + cD * L))) =
      2 ^ (A1c * (K + L) + B * (L * L) + cm * (K + L) + dQ * (K + L) + (Qv * d) * (K + cD * L)) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  calc max 1 Vl * 2 ^ m * (Qv * (Df + 1) ^ (Qv * d))
      ≤ 2 ^ (A1c * (K + L) + B * (L * L)) * 2 ^ (cm * (K + L)) * (2 ^ (dQ * (K + L)) * 2 ^ ((Qv * d) * (K + cD * L))) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (Nat.mul_le_mul h3 h4)
    _ = 2 ^ (A1c * (K + L) + B * (L * L) + cm * (K + L) + dQ * (K + L) + (Qv * d) * (K + cD * L)) := hE
    _ ≤ 2 ^ (coOf (A1c + B + cm) dQ cD dD * U) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have e : coOf (A1c + B + cm) dQ cD dD * U = (A1c + B + cm + 400 + dQ) * U + cD * dQ * dD * U := by
          unfold coOf; ring
        omega

section Gate
variable (l : Literals) (F : GateFree l)

/-- **`hrange` at a THR call** (ThrEAt3's range clause) at `freeProg2 (thrK2 c)`, `d_Q ≥ cST + 1`. -/
theorem hrange_thr (c : SymC) (hdQ : cST l F.filterErrDeg + 1 ≤ c.dQ) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ∀ p' : List Bool, p'.length ≤ 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell → ∀ z,
      (2 : ℤ) ^ (((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) - 1) *
        SeedFix.sampElim (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
          (SeedFix.thrStateBits (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation z) p'.length
          (SeedFix.listNum p') < 2 ^ ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) := by
  intro p' hp' z
  have hNT := thrNT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hQ := thrCount_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hl := thrEll_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hm := m_le_thr l F c kclk coef A a ha ha' Cs carriers translation hcall hs
  have hv2 := Qp_eq_thr l F c kclk coef A a ha Cs carriers hs
  have hL1 := one_le_L n
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hNT hQ hl hm hv2
  rw [← hKd] at hkh
  rw [← hLd] at hL1
  refine sampElim_lt _ _ _ _ hp' _ _ (eNT l F.filterErrDeg * (K + L)) (eQT l F.filterErrDeg * (K + L))
    (by rw [← Enum.thrNT_eq_card]; exact hNT) hQ ?_
  rw [hv2]
  have hdq : (cST l F.filterErrDeg + 1) * (K + L) ≤ c.dQ * (K + L) := Nat.mul_le_mul_right _ hdQ
  have hl' : 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell ≤ 8 * ((eQT l F.filterErrDeg + 2) * (K + L)) := Nat.mul_le_mul_left _ hl
  have hkh' : (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).kh = SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) := rfl
  have e2 : (cST l F.filterErrDeg + 1) * (K + L) = 16 * (eQT l F.filterErrDeg * (K + L)) +
      eNT l F.filterErrDeg * (K + L) + 160 * CallIndex.algX l * (K + L) + 601 * (K + L) := by unfold cST; ring
  have e3 : 8 * ((eQT l F.filterErrDeg + 2) * (K + L)) = 8 * (eQT l F.filterErrDeg * (K + L)) + 16 * (K + L) := by ring
  have e4 : (16 + 16 * (10 * CallIndex.algX l + 32)) * (K + L) = 160 * CallIndex.algX l * (K + L) + 528 * (K + L) := by
    ring
  have hKL : 1 ≤ K + L := by omega
  rw [hkh']
  omega

/-- **The THR request's numbers below `2^{e_F}`**: the fixed fields' base and the displayed parameters. -/
theorem thrFix_le (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    FinalPass.EnumCap.fixB (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) + bnOf (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) ≤
      2 ^ efOf (cDa (gate0 l F).alg + cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2))) (Nat.clog 2 (n + 2)) := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hP := thrPool_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hD := thrD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
  have hm := m_le_thr l F c kclk coef A a ha ha' Cs carriers translation hcall hs
  have hQ := Qp_eq_thr l F c kclk coef A a ha Cs carriers hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hL1 := one_le_L n
  have hn2 := n2_le_L n
  have hN := n26_le n
  have hcD : 1 ≤ cDa (gate0 l F).alg := by unfold cDa; omega
  have hcm : 1 ≤ cmT l := by unfold cmT; omega
  have hdr := two_dRow_le ((callInputs l F kclk coef A a ha).starParams n hs)
  have hwd := FinalPass.C3Geo.width_le_dRow ((callInputs l F kclk coef A a ha).starParams n hs)
  have hDl : (Pool.densePool (gate0 l F).alg ((Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).length ≤ 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n + 26 * Nat.clog 2 (n + 2) + 5) := by
    rw [dense_length, List.length_map]
    have hfl : (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length =
        4 * (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) * 2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) := by
      simp [PrimT.C4Geo.flips]
    rw [hfl, ← pow_add, ← two_mul, hkh, pow_add, pow_add]
    have h1 : 4 * 2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤
        4 * 2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * (8 * 2 ^ (26 * Nat.clog 2 (n + 2))) := Nat.mul_le_mul_left _ (by omega)
    have e : 4 * 2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * (8 * 2 ^ (26 * Nat.clog 2 (n + 2))) =
        2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * 2 ^ (26 * Nat.clog 2 (n + 2)) * 2 ^ 5 := by ring
    omega
  have hPex : (Pool.poolChildren (gate0 l F).alg ((Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).length ≤
      (Pool.densePool (gate0 l F).alg ((Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).flatten.length :=
    ((Emit.shapeOf_flatten_length _ _ _ _ _).symm.trans (Top.shapeOf_flatten_len _)).le
  have hcols : (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams n hs)).length = PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) := by
    simp [PrimT.C4Geo.cols]
  have hrn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
  rw [hrn] at hdr
  have hw1 : PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs) ≤ n + 1 := by omega
  have hd1 : PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) ≤ n + 1 := by omega
  have hc1 : (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams n hs)).length ≤ n + 1 := by rw [hcols]; exact hd1
  have hdg : thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) = c.dD * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2)) := by
    show c.dD * (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) = _
    rw [sT_add]
  have key := fix_numT (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2))) n (cDa (gate0 l F).alg)
    (cmT l) c.dQ c.dD c.dH c.eH c.dP c.eP (m := ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4)) (h := ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3))
    (pr := ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5)) (dg := thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs))
    _ _ _ _ _ _ _ hL1 hn2 hcD hcm hQ hD hDl hm rfl rfl hw1 hd1 hc1 hdg hPex
  unfold FinalPass.EnumCap.fixB bnOf
  exact key

/-- **The charged occurrence count at every prefix** of a THR call below `2^{c_O U}`. -/
theorem thrOcc_le (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (p' : List Bool) :
    (PrimT.C4Child.chR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1) (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) p').occBoundP (gate0 l F).alg ≤
      2 ^ (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD *
        ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2)))) := by
  have hV := lenV_thr l F kclk coef A a ha ha' Cs carriers translation hcall hs p'.length (SeedFix.listNum p')
  have hD := thrD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
  have hm := m_le_thr l F c kclk coef A a ha ha' Cs carriers translation hcall hs
  have hQ := Qp_eq_thr l F c kclk coef A a ha Cs carriers hs
  have hcD : 1 ≤ cDa (gate0 l F).alg := by unfold cDa; omega
  have hLL : Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2) ≤ sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2) := by
    rw [sT_add]; omega
  have hdg : thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) = c.dD * (sT (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2)) := by
    show c.dD * (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2)) + Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) = _
    rw [sT_add]
  generalize (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) = nT at hV ⊢
  unfold Req.C3Req.occBoundP
  exact occ_numT _ _ _ _ _ _ _ _ _ _ _ _ _ _ (one_le_L n) hcD hLL hV hm hQ hD hdg

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
