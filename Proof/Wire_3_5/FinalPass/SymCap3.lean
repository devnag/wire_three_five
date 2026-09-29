import Proof.Wire_3_5.FinalPass.SymCap2
import Proof.Wire_3_5.FinalPass.SymHp3
import Proof.Wire_3_5.Primitive.SeedFix.C4PadA

/-! # The SYM enumeration's capacity, part 3: `EnumOk` at every SYM call

P3:3011-3016, 2987-2988 at a SYM call, with the free numbers `TWd = d_T L²`, `Cap = 2^{⌊n/16⌋ + d_C L²}` (the v2
program) and the cell cost bound `K(n) = 2^{⌊n/16⌋ + d_C L²}`: `n_T ≤ 2^{TWd}` (`2e_N ≤ d_T`), `Q ≥ 1`, and the group
size bound `capC·(qG(8ℓ)+1)^6 ≤ Cap` under the load floor `16·symC1 ≤ C_D` (with `1 ≤ c_ψ`: `ψ ≤ n`) and
`symDC ≤ d_C`; so the enumeration's hypotheses hold at every child prefix (the generic `EnumCap.enumOk_of`, SYM as one
instance). Also `Q' ≤ pr` and `1 ≤ h` at the call.

* `symKn`, **`hnT_sym`**, **`hQ_sym`**, `hQp_sym`, `one_le_h_sym`;
* **`symQ_of`**, **`symHok_of`** (generic in the call's batch, `R ≤ 10`, the degree bound `D`), their instances
  **`symQ_le`**, **`symHok`** (the SYM batch, `D = symDg`) and **`padHok`** (the degenerate call's padded batch,
  `R′ = 1`, `D = 0`; v7's `SymPadEAt.hok`).

Paper quantity of the main type: the enumeration's hypotheses at a SYM call's child prefixes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

/-- The cell cost bound `K(n) = 2^{⌊n/16⌋ + d_C L²}` (the capacity's value). -/
def symKn (c : SymC) (n : ℕ) : ℕ := 2 ^ (n / 16 + c.dC * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)))

section Gate
variable (l : Literals) (F : GateFree l)

/-- **`n_T ≤ 2^{TWd}`** at a SYM call (`TWd = d_T·β²`, `2e_N ≤ d_T`). -/
theorem hnT_sym (c : SymC) (hdT : 2 * eN l F.filterErrDeg ≤ c.dT) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers ≤
      2 ^ (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 0 := by
  have h := symNT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
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
  calc eN l F.filterErrDeg * (K + Nat.clog 2 (n + 2)) ≤ eN l F.filterErrDeg * (2 * S) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 2 * eN l F.filterErrDeg * S := by ring
    _ ≤ c.dT * S := Nat.mul_le_mul_right _ hdT

/-- **`Q ≥ 1`** at a SYM call. -/
theorem hQ_sym (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    1 ≤ (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).Q := by
  have hn8 := HashFam.fam_n8 l F kclk coef A a ha hs
  show 1 ≤ SeedFix.symCount _ _ _ _
  unfold SeedFix.symCount Sampler.sampleCount
  have hn : 0 < n := by omega
  show 0 < _
  positivity

/-- `Q' ≤ pr` at a SYM call (`2d_Q ≤ d_P`, `1 ≤ e_P`). -/
theorem hQp_sym (c : SymC) (hdP : 2 * c.dQ ≤ c.dP) (heP : 1 ≤ c.eP) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2 ≤
      (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5 := by
  rw [Qp_eq l F c kclk coef A a ha Cs carriers hs]
  have hkL := kL_le_n l F kclk coef A a ha ha' Cs carriers translation hcall
  show _ ≤ c.dP * (n + 1) ^ c.eP
  have h1 : n + 1 ≤ (n + 1) ^ c.eP := Nat.le_self_pow (by omega) _
  calc c.dQ * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) ≤ c.dQ * (2 * (n + 1)) :=
        Nat.mul_le_mul_left _ hkL
    _ = 2 * c.dQ * (n + 1) := by ring
    _ ≤ c.dP * (n + 1) ^ c.eP := Nat.mul_le_mul hdP h1

/-- `1 ≤ h` at a SYM call (`1 ≤ d_H`). -/
theorem one_le_h_sym (c : SymC) (hdH : 1 ≤ c.dH) (x : FreeIn) : 1 ≤ (freeProg2 (symK2 c)).val x 3 := by
  show 1 ≤ c.dH * (x.n + 1) ^ c.eH
  exact Nat.mul_le_mul hdH (Nat.one_le_pow _ _ (by omega))

/-- **The group size bound below the capacity** at a SYM call, generic in the batch (`R ≤ 10`, rows' words below
`2^{(26L+7)D + k + 80L + 24}`, `D` below the SYM degree bound), under the load floor. -/
theorem symQ_of (c : SymC) (hCD : 16 * symC1 (eN l F.filterErrDeg) (eQ l F.filterErrDeg) (CallIndexR.capZR l) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi) (hdC : symDC c.dT F.filterErrDeg ≤ c.dC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Rn Dg : ℕ) (batch : List SeedFix.SExpr) (hR : Rn ≤ 10)
    (hb : PrimT.C4Grp.bsz batch ≤ 2 ^ ((26 * Nat.clog 2 (n + 2) + 7) * Dg +
        ((gate0 l F).budget kclk coef A a ha).kOf n + 80 * Nat.clog 2 (n + 2) + 24))
    (hDg : Dg ≤ 384 * (F.filterErrDeg * Nat.clog 2 (n + 2) + 1) + 1 +
      3 * ((71 + 12 * ((gate0 l F).budget kclk coef A a ha).kOf n + CallIndexR.capZR l * Nat.clog 2 (n + 2)) *
        (23296 * Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n) + 23553))) :
    EnumCap.capC * (PrimT.C4Grp.qG (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers)
      (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) Rn (PrimT.C4Grp.bsz batch)
      (c.dT * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)))
      (8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell) + 1) ^ 6 ≤ symKn c n := by
  have hnT := symNT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hq := EnumCap.qG_lt_pow (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers)
    (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) Rn (PrimT.C4Grp.bsz batch)
    (c.dT * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)))
    (8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell) _ _
    (PrimT.C4Grp.bsz_pos _) hb hnT
  have hq6 := pow_mono_mul 6 hq
  have hell := ell_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  -- the load
  have hsy := loadSym_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
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
  have hnum := symE_num (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
    (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n))
    (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell
    (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).kh Rn
    Dg F.filterErrDeg (CallIndexR.capZR l) (eN l F.filterErrDeg)
    (eQ l F.filterErrDeg) c.dT c.dC F.CD (((gate0 l F).budget kclk coef A a ha).psiOf n) n (one_le_L n) hell
    (by show SeedFix.callKh _ ≤ _; omega) hR hDg hsy hn hCD hdC
  unfold EnumCap.xG at hq6
  have hC : EnumCap.capC ≤ 2 ^ 17 := by unfold EnumCap.capC; norm_num
  calc EnumCap.capC * (_ + 1) ^ 6 ≤ 2 ^ 17 * 2 ^ (6 * (eN l F.filterErrDeg * (((gate0 l F).budget kclk coef A a ha).kOf n +
        Nat.clog 2 (n + 2)) + 2 * (14 + 24 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell +
        40 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).kh +
        c.dT * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) +
        8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell + 8 * Rn) +
        (8 * Rn + 1) * ((26 * Nat.clog 2 (n + 2) + 7) * Dg +
          ((gate0 l F).budget kclk coef A a ha).kOf n + 80 * Nat.clog 2 (n + 2) + 24) + 5)) := Nat.mul_le_mul hC hq6
    _ = 2 ^ (17 + 6 * (eN l F.filterErrDeg * (((gate0 l F).budget kclk coef A a ha).kOf n +
        Nat.clog 2 (n + 2)) + 2 * (14 + 24 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell +
        40 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).kh +
        c.dT * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) +
        8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell + 8 * Rn) +
        (8 * Rn + 1) * ((26 * Nat.clog 2 (n + 2) + 7) * Dg +
          ((gate0 l F).budget kclk coef A a ha).kOf n + 80 * Nat.clog 2 (n + 2) + 24) + 5)) := by rw [pow_add]
    _ ≤ symKn c n := Nat.pow_le_pow_right (by norm_num) hnum

/-- **The enumeration's hypotheses at every child prefix of a SYM call**, generic in the batch (`±1` coefficients,
`R ≤ 10`, rows' words and `D` as in `symQ_of`), at `K = symKn`. -/
theorem symHok_of (c : SymC) (hdT : 2 * eN l F.filterErrDeg ≤ c.dT)
    (hCD : 16 * symC1 (eN l F.filterErrDeg) (eQ l F.filterErrDeg) (CallIndexR.capZR l) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi) (hdC : symDC c.dT F.filterErrDeg ≤ c.dC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Rn Dg : ℕ) (batch : List SeedFix.SExpr) (hR : Rn ≤ 10)
    (hpm : ∀ V ∈ batch, ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1)
    (hb : PrimT.C4Grp.bsz batch ≤ 2 ^ ((26 * Nat.clog 2 (n + 2) + 7) * Dg +
        ((gate0 l F).budget kclk coef A a ha).kOf n + 80 * Nat.clog 2 (n + 2) + 24))
    (hDg : Dg ≤ 384 * (F.filterErrDeg * Nat.clog 2 (n + 2) + 1) + 1 +
      3 * ((71 + 12 * ((gate0 l F).budget kclk coef A a ha).kOf n + CallIndexR.capZR l * Nat.clog 2 (n + 2)) *
        (23296 * Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n) + 23553))) :
    ∀ (p : List Bool) (b : Bool), p.length < 8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell →
      PrimT.C4Dock.EnumOk (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers)
        (SeedFix.JLink.chunk (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
          (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) Rn batch)
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 0)
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 1)
        (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) Rn (symKn c n) batch (p ++ [b]) := by
  intro p b hp
  have hQ := symQ_of l F c hCD hcpsi hdC kclk coef A a ha ha' Cs carriers translation hcall hs Rn Dg batch hR hb hDg
  have h6 : 6000 ≤ EnumCap.capC := by unfold EnumCap.capC; norm_num
  exact EnumCap.enumOk_of _ _ _ _ _ _ _ _ hpm (hQ_sym l F kclk coef A a ha Cs carriers hs)
    (hnT_sym l F c hdT kclk coef A a ha ha' Cs carriers translation hcall hs) le_rfl hQ
    ((Nat.mul_le_mul_right _ h6).trans hQ) p b hp

/-- **SymEAt3's `hok` at a SYM call** (the SYM batch, `D = symDg`). -/
theorem symHok (c : SymC) (hdT : 2 * eN l F.filterErrDeg ≤ c.dT)
    (hCD : 16 * symC1 (eN l F.filterErrDeg) (eQ l F.filterErrDeg) (CallIndexR.capZR l) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi) (hdC : symDC c.dT F.filterErrDeg ≤ c.dC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ∀ (p : List Bool) (b : Bool), p.length < 8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell →
      PrimT.C4Dock.EnumOk (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers)
        (symEnts (callInputs l F kclk coef A a ha) hs Cs carriers)
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 0)
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 1)
        (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) (carriers.length + 2 * a') (symKn c n)
        (symExprs (callInputs l F kclk coef A a ha) hs Cs carriers) (p ++ [b]) := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  exact symHok_of l F c hdT hCD hcpsi hdC kclk coef A a ha ha' Cs carriers translation hcall hs _ _ _ (by omega)
    (BShape.sym_coef_pm1 _ hs Cs carriers) (symBsz_le l F kclk coef A a ha ha' Cs carriers translation hcall hs)
    (symDg_le l F kclk coef A a ha ha' Cs carriers translation hcall hs)

/-- The constant row's word. -/
theorem constRow_word : (ListMachine.Rec.exprWord PrimT.C4Pad.constRow).length ≤ 2 ^ 24 := by decide

/-- **v7's `SymPadEAt.hok` at a degenerate SYM call**: the padded batch (the constant row per entry, `R′ = 1`). -/
theorem padHok (c : SymC) (hdT : 2 * eN l F.filterErrDeg ≤ c.dT)
    (hCD : 16 * symC1 (eN l F.filterErrDeg) (eQ l F.filterErrDeg) (CallIndexR.capZR l) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi) (hdC : symDC c.dT F.filterErrDeg ≤ c.dC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ∀ (p : List Bool) (b : Bool), p.length < 8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell →
      PrimT.C4Dock.EnumOk (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers)
        (SeedFix.JLink.chunk (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
          (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) 1
          (PrimT.C4Pad.padBatch (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
            (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers)))
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 0)
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 1)
        (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) 1 (symKn c n)
        (PrimT.C4Pad.padBatch (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
          (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers)) (p ++ [b]) := by
  have hmem : ∀ V ∈ PrimT.C4Pad.padBatch (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
      (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers), V = PrimT.C4Pad.constRow :=
    fun V hV => List.eq_of_mem_replicate hV
  have h24 : (2 : ℕ) ^ 24 ≤ 2 ^ ((26 * Nat.clog 2 (n + 2) + 7) * 0 +
      ((gate0 l F).budget kclk coef A a ha).kOf n + 80 * Nat.clog 2 (n + 2) + 24) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  refine symHok_of l F c hdT hCD hcpsi hdC kclk coef A a ha ha' Cs carriers translation hcall hs 1 0 _ (by norm_num)
    (fun V hV t ht => ?_) (EnumCap.bsz_le _ _ Nat.one_le_two_pow (fun V hV => ?_)) (Nat.zero_le _)
  · rw [hmem V hV] at ht
    simp only [PrimT.C4Pad.constRow, List.mem_singleton] at ht
    subst ht
    left; rfl
  · rw [hmem V hV]
    exact constRow_word.trans h24

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
