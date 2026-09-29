import Proof.Wire_3_5.Primitive.Writers.ThrSide4

/-! # c4 THR block, piece 6 part 5: the THR free numbers and the enumeration's side conditions (`hok`)

The THR twin of the SymFr3/SymCap3 at the THR call: the free numbers `freeVal2 (thrK2 c) (thrX …)` (`m =
max(8·|carriers| + 16·τ₀, 8)`: the carrier rows have one factor, the RADIX row `2τ₀`, BShape5's
`thr_rows_factors`), the requests' degree bound `thrDF c x = d_D(⌊√(B_T L)⌋ + L²)` (the paper's `d_T`,
P3:3094-3100); at a THR call `n_T ≤ 2^{TWd}`, `Q ≥ 1`, `Q' ≤ pr`, `1 ≤ h`, and the enumeration's hypotheses at every
child prefix (`EnumCap.enumOk_of`, the capacity `2^{⌊n/16⌋ + d_C L²}`) under the THR load floor.

* **`thrK2`**, **`thrDF`**; `hnT_thr`, `hQ_thr`, `hQp_thr`, **`thrQ_of`**, **`thrHok`**.

Paper quantities of the main types: the THR free numbers and the enumeration's hypotheses at a THR call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC symKn cK pow_N_le one_le_L n2_le_L kh_two cr_le_k
  pow_mono_mul k_le_L2)

/-- **The THR constants**: `m = max(8·|carriers| + 16·τ₀, 8)` (the field `M` of `thrX` is the digit count `τ₀`). -/
def thrK2 (c : SymC) : FreeK2 := ⟨⟨c.dT, c.dC, c.dQ, c.dH, 8, 0, 0, 0, 0, 16, c.dP, c.dA, c.dR⟩, c.eH, c.eP, 8⟩

/-- **The THR requests' degree bound** `d_D(⌊√(B_T L)⌋ + L²)` (the paper's `d_T = C_D(√(B_T L) + L²)`). -/
def thrDF (c : SymC) (x : FreeIn) : ℕ := c.dD * (Nat.sqrt (x.capS * β x) + β x * β x)

section Gate
variable (l : Literals) (F : GateFree l)

/-- **`n_T ≤ 2^{TWd}`** at a THR call (`TWd = d_T·β²`, `2e_N ≤ d_T`). -/
theorem hnT_thr (c : SymC) (hdT : 2 * eNT l F.filterErrDeg ≤ c.dT) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
      2 ^ (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 0 := by
  have h := thrNT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hk := k_le_L2 l F kclk coef A a ha hs
  have hL := Nat.le_self_pow (show 2 ≠ 0 by norm_num) (Nat.clog 2 (n + 2))
  refine h.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  show _ ≤ c.dT * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))
  rw [← sq]
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨S, hSd⟩ : ∃ S, S = Nat.clog 2 (n + 2) ^ 2 := ⟨_, rfl⟩
  rw [← hKd, ← hSd] at hk
  rw [← hSd] at hL
  rw [← hKd, ← hSd]
  calc eNT l F.filterErrDeg * (K + Nat.clog 2 (n + 2)) ≤ eNT l F.filterErrDeg * (2 * S) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 2 * eNT l F.filterErrDeg * S := by ring
    _ ≤ c.dT * S := Nat.mul_le_mul_right _ hdT

/-- **`Q ≥ 1`** at a THR call. -/
theorem hQ_thr (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    1 ≤ (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).Q := by
  have hn8 := HashFam.fam_n8 l F kclk coef A a ha hs
  show 1 ≤ SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs
  rw [ThrQ.thrCount_eq]
  unfold ThrQ.thrQval Sampler.sampleCount
  have hn : 0 < n := by omega
  exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.succ_pos _)) (pow_pos hn _))

/-- **`Q' ≤ pr`** at a THR call (`2d_Q ≤ d_P`, `1 ≤ e_P`). -/
theorem hQp_thr (c : SymC) (hdP : 2 * c.dQ ≤ c.dP) (heP : 1 ≤ c.eP) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 ≤
      (freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 := by
  have hkh := kh_two l F kclk coef A a ha hs
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ n := hcall.2.2.2.2.2.2.kq
  have hL : Nat.clog 2 (n + 2) ≤ n + 1 := Nat.clog_le_of_le_pow (by
    have := Nat.lt_two_pow_self (n := n + 1)
    rw [pow_succ] at this ⊢; omega)
  show c.dQ * (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) +
    SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + Nat.clog 2 (n + 2)) ≤ c.dP * (n + 1) ^ c.eP
  have h1 : n + 1 ≤ (n + 1) ^ c.eP := Nat.le_self_pow (by omega) _
  calc c.dQ * (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) +
        SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + Nat.clog 2 (n + 2)) ≤
        c.dQ * (2 * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * c.dQ * (n + 1) := by ring
    _ ≤ c.dP * (n + 1) ^ c.eP := Nat.mul_le_mul hdP h1

/-- **The THR enumeration's group size bound below the capacity**, under the THR load floor. -/
theorem thrQ_of (c : SymC)
    (hCD : 16 * thrC1 (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) (10 * CallIndex.algX l + 32)
      (dDT l F.filterErrDeg) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi) (hdC : 12 * c.dT ≤ c.dC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    FinalPass.EnumCap.capC * (PrimT.C4Grp.qG (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1)
      (PrimT.C4Grp.bsz (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation))
      (c.dT * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)))
      (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) + 1) ^ 6 ≤ symKn c n := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hnT := thrNT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hq := FinalPass.EnumCap.qG_lt_pow (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1)
    (PrimT.C4Grp.bsz (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation))
    (c.dT * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)))
    (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) _ _
    (PrimT.C4Grp.bsz_pos _) (thrBsz_le l F kclk coef A a ha ha' Cs carriers translation hcall hs) hnT
  have hq6 := pow_mono_mul 6 hq
  have hell := thrEll_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hdig := dig_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hD := thrDg_lin l F kclk coef A a ha ha' Cs carriers translation hcall hs
  -- the load
  have hsy := loadThr_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
    (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hψ : ((gate0 l F).budget kclk coef A a ha).psiOf n = loadPsi F.CD (((gate0 l F).budget kclk coef A a ha).kOf n)
      (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n)
      (((gate0 l F).budget kclk coef A a ha).capOf .sym n) := rfl
  rw [← hψ] at hsy
  have hfits := hcall.2.2.2.2.2.2.pre
  have hcp : 1 ≤ (gate0 l F).E.cpsi := hcpsi
  have hn : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤ n := by
    have : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤
        (gate0 l F).E.cpsi * ((gate0 l F).budget kclk coef A a ha).psiOf n := Nat.le_mul_of_pos_left _ hcp
    exact this.trans (le_trans (Nat.le_add_right _ _) hfits)
  have hnum := thrE_num (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
    (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2)))
    (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell
    (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).kh (carriers.length + 1)
    (thrDg l F kclk coef A a ha Cs carriers translation hs)
    (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) c.dT c.dC F.CD (((gate0 l F).budget kclk coef A a ha).psiOf n) n
    (10 * CallIndex.algX l + 32) (dDT l F.filterErrDeg) (one_le_L n) hell
    (by show SeedFix.callKh _ ≤ _; omega) (by omega) hdig hD hsy hn hCD hdC
  unfold FinalPass.EnumCap.xG at hq6
  have hC : FinalPass.EnumCap.capC ≤ 2 ^ 17 := by unfold FinalPass.EnumCap.capC; norm_num
  refine (Nat.mul_le_mul hC hq6).trans ?_
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) hnum

/-- **ThrEAt3's `hok` at a THR call** (the THR batch, `K = symKn c`). -/
theorem thrHok (c : SymC) (hdT : 2 * eNT l F.filterErrDeg ≤ c.dT)
    (hCD : 16 * thrC1 (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) (10 * CallIndex.algX l + 32)
      (dDT l F.filterErrDeg) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi) (hdC : 12 * c.dT ≤ c.dC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ∀ (p : List Bool) (b : Bool), p.length < 8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell →
      PrimT.C4Dock.EnumOk (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
        (thrEnts (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
        ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 0)
        ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1)
        (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (carriers.length + 1) (symKn c n)
        (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (p ++ [b]) := by
  intro p b hp
  have hQ := thrQ_of l F c hCD hcpsi hdC kclk coef A a ha ha' Cs carriers translation hcall hs
  have h6 : 6000 ≤ FinalPass.EnumCap.capC := by unfold FinalPass.EnumCap.capC; norm_num
  exact FinalPass.EnumCap.enumOk_of _ _ _ _ _ _ _ _
    (fun V hV t ht => Or.inl (BShape.thr_coef_one (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers
      translation V hV t ht))
    (hQ_thr l F kclk coef A a ha Cs hs)
    (hnT_thr l F c hdT kclk coef A a ha ha' Cs carriers translation hcall hs) le_rfl hQ
    ((Nat.mul_le_mul_right _ h6).trans hQ) p b hp

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
