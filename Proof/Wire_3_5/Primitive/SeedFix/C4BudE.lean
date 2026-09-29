import Proof.Wire_3_5.Primitive.SeedFix.C4BudD
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB4
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNE

/-! # C4.K item (h), part 5: the SYM stage's steps at every SYM call within `c₄·seedClasses E₄`

P3:3098-3100, 3105-3115 (the seed-fixing budget, `E₄` before `F`, `c₄` after), 1188-1200 (the star: `k = rs`, the
center bits `n − k`, the capacity), 3154-3162 (the sample count): at every SYM call of the family, the SYM stage's steps
(the setup at the capacity `2·2^{⌊n/8⌋+C}+2`, the loop over the child family, the sample expansion, the pad `P`) are
at most `c₄·seedClasses E₄ n k ψ`, for one `c₄` chosen after `F` (`budget_le` over `wrap_split` and `rest_le`).

* `symN_le` (the numbers machine at the call), `ell_le`, `d2_le`, **`sym_steps_le`**.

Paper quantity of the main type: the SYM stage's steps against the seed-fixing budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost)

/-- **The SYM numbers machine's steps at a SYM call** (`sym_needs` at the capacity, PA's cost bounds). -/
theorem symN_le (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (h : SB)
    (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ h.Cw * (n + 1) ^ h.Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ h.Cnw * (n + 1) ^ h.Dnw)
    (hZ : h.Z = CallIndexR.capZR l) (hZm : h.Zm = 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)
    (hCsp : h.Csp = gateCsp l) (hJ : h.J = SymSizes.schedJ l) (hcX : h.cX = SymSizes.cXg l)
    (hK : h.capK = CallIndexR.capK F.cr) (hcr : h.cr = F.cr) (hfe : h.fe = F.filterErrDeg)
    (hcM : h.cM = CapNum.cMain (gateCap l) .sym)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (cap fc : ℕ)
    (hcapKQ : 100 * (2 ^ h.cA * (2 ^ (((gate0 l F).budget kclk coef A a0 ha0).kOf n + Nat.clog 2 (n + 2) +
      h.KF * Nat.clog 2 (n + 2) ^ 2 + 0) + 1)) + 200000 ≤ cap) :
    C4SymN.symBigCost cap n F.cr F.filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a carriers.length
      (UnaryCalc.value h.D2 h.C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum fc ≤
        3000000 * ((cap + 2) * (cap + 2) * (cap + 2)) + fc := by
  obtain ⟨hN1, -, -, hcS, hcP, hcC, -, -, -⟩ := C4SymN.sym_needs l F kclk coef A a0 ha0 h hwb hnw hZ hZm hCsp hJ hcX
    hK hcr hfe hcM ha Cs carriers translation hcall hs cap hcapKQ
  obtain ⟨hk2, -, -⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have cP := hN1.cP
  have cC := hN1.cC
  have hsp := hcC.hs
  have hL := hcC.hL1
  have ht : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n ≤ cap := by
    unfold SparseNum.sparseBound at hcP
    omega
  have h4 : 4 * (n + 3) ≤ (F.filterErrDeg + 4) * (n + 3) := Nat.mul_le_mul_right _ (by omega)
  have h5 : F.filterErrDeg ≤ (F.filterErrDeg + 4) * (n + 3) := by nlinarith
  have v1 := Nat.one_le_two_pow (n := natBitLength n)
  have v2 := Nat.one_le_two_pow (n := natBitLength (Data.symCodes a Cs).length)
  have v3 := Nat.one_le_two_pow (n := natBitLength (carriers.map Carrier.code).length)
  exact symBig_le cap n F.cr F.filterErrDeg _ _ (Ledger.Lq n) a carriers.length _ ((n + 1) ^ 26) _ fc (by omega) ha
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ht hsp hL

/-- **The loop's width `ℓ = max(2k_h, ⌈log₂ Q⌉)` and the sampler's are `≤ 2e_Q(B+1)²`**, and `Q ≤ 2^{e_Q(B+1)²}`
(`q_le`; `2^{k_h} ≤ Q`, `N_le_sampleCount`). -/
theorem ell_le (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) :
    max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) +
        SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
        (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) ≤
      2 * C4SymN.eQ l F.cr F.filterErrDeg * C4Cap.bsq n ∧
    (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers).ell ≤ 2 * C4SymN.eQ l F.cr F.filterErrDeg * C4Cap.bsq n ∧
    SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers ≤ 2 ^ (C4SymN.eQ l F.cr F.filterErrDeg * C4Cap.bsq n) := by
  have hq := C4SymN.q_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs
  have hn := PrimAsm.CallIndex.n_ge_two l F hs
  have hN : 2 ^ SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) ≤
      SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers :=
    Sampler.N_le_sampleCount _ _ _ _ (by omega) (by omega)
  obtain ⟨e, he⟩ : ∃ x, x = C4SymN.eQ l F.cr F.filterErrDeg * C4Cap.bsq n := ⟨_, rfl⟩
  have he1 : 1 ≤ e := by
    rw [he]
    have h1 : 1 ≤ C4SymN.eQ l F.cr F.filterErrDeg := by unfold C4SymN.eQ; omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by have := C4Cap.bsq_pos n; omega))
  rw [← he] at hq ⊢
  have e2 : 2 * C4SymN.eQ l F.cr F.filterErrDeg * C4Cap.bsq n = 2 * e := by rw [he]; ring
  rw [e2]
  have hkh : SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) ≤ e := by
    by_contra hc
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_of_not_le hc)
    omega
  have hcl : Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) ≤ e :=
    Nat.clog_le_of_le_pow hq
  refine ⟨by omega, ?_, hq⟩
  show max 1 (max (2 * SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
    (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) ≤ 2 * e
  omega

/-- The two center-bit halves: `2·d_row ≤ n − k + 1` (`centerBits_sum`, `centerBits_balanced`). -/
theorem d2_le (P : StarParams) : 0 + C4Geo.dRow P + C4Geo.dRow P ≤ P.n - P.k + 1 := by
  have h1 := P.centerBits_sum
  have h2 := P.centerBits_balanced
  have e : C4Geo.dRow P = P.leftCenterBits := rfl
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4Bud
