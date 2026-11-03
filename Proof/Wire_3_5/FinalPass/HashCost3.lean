import Lean
import Proof.Wire_3_5.FinalPass.HashCost2
import Proof.Wire_3_5.FinalPass.HashOccBase
import Proof.Wire_3_5.FinalPass.HashPre1Base
import Proof.Wire_3_5.Primitive.Writers.ThrSide6Base
import Proof.Wire_3_5.FinalPass.HashPadBase
import Proof.Wire_3_5.FinalPass.EnumCap7
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashCost1
import Proof.Wire_3_5.FinalPass.HashOcc
import Proof.Wire_3_5.FinalPass.HashPre1
import Proof.Wire_3_5.FinalPass.HashRange
import Proof.Wire_3_5.FinalPass.HashS
import Proof.Wire_3_5.FinalPass.HashSz1
import Proof.Wire_3_5.FinalPass.HashSz2
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrSide6
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.HashCost3Base


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH child's cost, part 3: `hcost` at a THR call's HASH stage

P3:2253-2290, 3011-3016, 3098-3107: one HASH child (the `hCoreCost`: the Hb prep, the Hb printer's `n` cells at the
cell bound `K_c = Cap = 2^{⌊n/16⌋ + d_C L²}`, the expression's terminator, C6's assembler and the printer child) runs
within `K_ch = symKch = 2^{n − k + d_A L − 4}` steps at every prefix of at most `s_h = 2tℓ₀` bits, from T3's
`HbPrepBound`, the Hb size `hbS ≤ 2^{2k + c_S X³}` below the capacity (`capS_hash`, which also gives the printer's
cell bound `2^{32}(hbS+1)^8 ≤ Cap`), the `asmCost_le`/`childCost_le` at `q = 2^{e_C}·2^{e_X}`, `c3Cost_le_B`,
the charged occurrences `≤ 2^{C₁ S_aux}` and the `kch_pow` (at `d_A − 1`), under the floors `occCDH`, `costCDH ≤ C_D`
and `dAH ≤ d_A` (all fixed before `F`).

* `aux_le`, `fixH_le`, `occP_hash`, **`capS_hash`**, **`hcost_hash`**.

Paper quantity of the main type: one HASH child's step count against the pad. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires.WireExponent3_5.CompilerMachine.Top NearCubicWires.RepairRepresentation

section Gate
variable (l : Literals) (F : GateFree l)

/-- `C_D·S_aux ≤ n` at a THR call (the auxiliary load, `ψ ≤ n` by the fit). -/
theorem aux_le (hcpsi : 1 ≤ F.E.cpsi) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation)) : F.CD * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) ≤ n := by
  have hfits := hcall.2.2.2.2.2.2.pre
  have hψ : ((gate0 l F).budget kclk coef A a ha).psiOf n = loadPsi F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n)
      (((gate0 l F).budget kclk coef A a ha).capOf .sym n) := rfl
  have hAux : loadAux F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) ≤ ((gate0 l F).budget kclk coef A a ha).psiOf n := by
    rw [hψ]; unfold loadPsi; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hcp : 1 ≤ (gate0 l F).E.cpsi := hcpsi
  have hn : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤ n := by
    have : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤
        (gate0 l F).E.cpsi * ((gate0 l F).budget kclk coef A a ha).psiOf n := Nat.le_mul_of_pos_left _ hcp
    exact this.trans (le_trans (Nat.le_add_right _ _) hfits)
  exact le_trans (le_of_eq rfl) (hAux.trans hn)

/-- **The fixed fields and the displayed parameters** `≤ 2^{e_F}`. -/
theorem fixH_le (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    EnumCap.fixB (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) + bnOf (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) ≤ 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cF1 l (gate0 l F).alg * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (c.eH + c.eP) * (Nat.clog 2 (n + 2)) + c0F c) := by
  have hkh := kh_two l F kclk coef A a ha hs
  have hL1 := one_le_L n
  have hn2 := n2_le_L n
  have htl := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hGl := G_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hD := PrimAsm.ThrSide.thrD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
  have hdr := two_dRow_le ((callInputs l F kclk coef A a ha).starParams n hs)
  have hwd := C3Geo.width_le_dRow ((callInputs l F kclk coef A a ha).starParams n hs)
  have hrn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
  rw [hrn] at hdr
  have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
  have hXX : ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have hXXX : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (((gate0 l F).budget kclk coef A a ha).kOf n) + cF1 l (gate0 l F).alg * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (c.eH + c.eP) * (Nat.clog 2 (n + 2)) + c.dQ + c.dH + c.dP + c.dD + 5 := ⟨_, rfl⟩
  have eZ : ((((gate0 l F).budget kclk coef A a ha).kOf n) + cF1 l (gate0 l F).alg * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (c.eH + c.eP) * (Nat.clog 2 (n + 2)) + c0F c) = Z + 5 := by rw [hZ]; unfold c0F; ring
  have eF1 : cF1 l (gate0 l F).alg * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = cDa (gate0 l F).alg * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 40 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by unfold cF1; ring
  have q : ∀ x e, x ≤ 2 ^ e → e ≤ Z → x ≤ 2 ^ Z := fun x e h he => h.trans (Nat.pow_le_pow_right (by norm_num) he)
  have i1 : (Nat.clog 2 (n + 2)) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by omega
  have i2 : cDa (gate0 l F).alg * (Nat.clog 2 (n + 2)) ≤ cDa (gate0 l F).alg * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ i1
  have i3 : 2 * cT l * ((Nat.clog 2 (n + 2)) + 1) ≤ 2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ (hXX.trans hXXX)
  have i4 : ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := hXX.trans hXXX
  have i5 : c.eH * (Nat.clog 2 (n + 2)) + c.eP * (Nat.clog 2 (n + 2)) = (c.eH + c.eP) * (Nat.clog 2 (n + 2)) := by ring
  -- the terms
  have tQ : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 ≤ 2 ^ Z := by
    show c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) ≤ _
    have h1 : (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)) ≤ (((gate0 l F).budget kclk coef A a ha).kOf n) + (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
      have e : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + 3 * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + 3 * (Nat.clog 2 (n + 2)) + 1 := by ring
      omega
    have h2 : c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) ≤ 2 ^ c.dQ * 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) :=
      Nat.mul_le_mul (lt_pow_self' _) (h1.trans (lt_pow_self' _))
    rw [← pow_add] at h2
    have h3 : c.dQ + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) ≤ Z := by
      have : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ 40 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by omega
      rw [hZ]; omega
    exact q _ _ h2 h3
  have tDf : (Pool.densePool (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers)
      ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0).gates (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).flatten.length ≤ 2 ^ Z :=
    q _ _ (by omega : _ ≤ 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cDa (gate0 l F).alg * (Nat.clog 2 (n + 2)))) (by rw [hZ]; omega)
  have tDl : (Pool.densePool (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers)
      ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0).gates (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).length ≤ 2 ^ Z := by
    rw [dense_length]
    have hgl : (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0).gates.length = (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length := by simp [PrimT.C4Geo.poolReq]
    rw [hgl]
    have hfl : (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length = 4 * (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) * 2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) := by
      simp [PrimT.C4Geo.flips]
    rw [hfl, ← pow_add, ← two_mul, hkh]
    have h1 : 4 * 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 5 + 26 * (Nat.clog 2 (n + 2))) := by
      have e : (2 : ℕ) ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 5 + 26 * (Nat.clog 2 (n + 2))) = 4 * 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * (8 * 2 ^ (26 * (Nat.clog 2 (n + 2)))) := by
        rw [pow_add, pow_add]; ring
      rw [e]
      exact Nat.mul_le_mul_left _ (by rw [pow_add] at hGl; omega)
    exact q _ _ h1 (by rw [hZ]; omega)
  have tm : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4 ≤ 2 ^ Z := by
    rw [m_hash l F c kclk coef A a ha Cs carriers hs]
    have h1 : 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 ≤ 2 ^ (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) := by
      have e : 2 * cT l * ((Nat.clog 2 (n + 2)) + 1) = 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) := by ring
      exact (show 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 ≤ 2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1 by omega).trans (lt_pow_self' _)
    exact q _ _ h1 (by rw [hZ]; omega)
  have th : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 ≤ 2 ^ Z := by
    have h1 : c.dH * (n + 1) ^ c.eH ≤ 2 ^ (c.dH + c.eH * (Nat.clog 2 (n + 2))) := polyN_le c.dH c.eH n (Nat.clog 2 (n + 2)) hn2
    exact q _ _ h1 (by rw [hZ]; omega)
  have tpr : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 ≤ 2 ^ Z := by
    have h1 : c.dP * (n + 1) ^ c.eP ≤ 2 ^ (c.dP + c.eP * (Nat.clog 2 (n + 2))) := polyN_le c.dP c.eP n (Nat.clog 2 (n + 2)) hn2
    exact q _ _ h1 (by rw [hZ]; omega)
  have hnL : n + 1 ≤ 2 ^ (Nat.clog 2 (n + 2)) := by omega
  have tw : PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs) ≤ 2 ^ Z := q _ _ (by omega : _ ≤ 2 ^ (Nat.clog 2 (n + 2))) (by rw [hZ]; omega)
  have tdR : PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) ≤ 2 ^ Z := q _ _ (by omega : _ ≤ 2 ^ (Nat.clog 2 (n + 2))) (by rw [hZ]; omega)
  have hcols : (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams n hs)).length = PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) := by simp [PrimT.C4Geo.cols]
  have tdg : hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) ≤ 2 ^ Z := by
    show c.dD * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ _
    have h1 : c.dD * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ 2 ^ c.dD * 2 ^ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
      refine Nat.mul_le_mul (lt_pow_self' _) (le_trans ?_ (lt_pow_self' _))
      have : ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul (by omega) (by omega)
      omega
    rw [← pow_add] at h1
    exact q _ _ h1 (by rw [hZ]; have := eF1; omega)
  have hPex : (Pool.poolChildren (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers)
      ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0).gates (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).length ≤
      (Pool.densePool (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers)
      ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0).gates (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).flatten.length :=
    ((Emit.shapeOf_flatten_length _ _ _ _ _).symm.trans (Top.shapeOf_flatten_len _)).le
  have t1 : 1 ≤ 2 ^ Z := Nat.one_le_two_pow
  unfold EnumCap.fixB bnOf
  rw [eZ, pow_add]
  show (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 + (Pool.densePool (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0).gates (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).flatten.length + (Pool.densePool (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0).gates (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).length + (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4 + (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 + (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 +
      PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) + (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams n hs)).length + 1 +
      ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 + PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs) + (Pool.poolChildren (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0).gates (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).length + (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 + (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 + hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) + 1) ≤ _
  rw [hcols]
  have e32 : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [e32]
  omega

/-- **The charged occurrence count** `≤ 2^{C₁ S_aux}` at every prefix. -/
theorem occP_hash (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (p' : List Bool) :
    (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').occBoundP (gate0 l F).alg ≤ 2 ^ (C1H l (gate0 l F).alg c * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2))))) := by
  have hV := lenV_le l F kclk coef A a ha ha' Cs carriers translation hcall hs p'.length (SeedFix.listNum p')
  have hD := PrimAsm.ThrSide.thrD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
  have h1 := occP_le_of (gate0 l F).alg (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p') ((((gate0 l F).budget kclk coef A a ha).kOf n) + cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) ((((gate0 l F).budget kclk coef A a ha).kOf n) + cDa (gate0 l F).alg * (Nat.clog 2 (n + 2))) hV hD
  refine h1.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  have hm : (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').m = 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 := m_hash l F c kclk coef A a ha Cs carriers hs
  have hQ : (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').P.Q = c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) := rfl
  have hd : (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').d = c.dD * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) := rfl
  rw [hm, hQ, hd]
  have h2 := occS_num (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (cV l) (cT l) c.dQ c.dD (cDa (gate0 l F).alg) ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) (one_le_L n)
    (kh_two l F kclk coef A a ha hs) (t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs) rfl
  have e : C1H l (gate0 l F).alg c = 4 * cV l + 4 * cT l + 3 * c.dQ + 2 * c.dQ * c.dD * (cDa (gate0 l F).alg + 1) + 3 := rfl
  rw [e]
  omega

/-- **The Hb size below the capacity**: `2^{32}(hbS + 1)^8 ≤ Cap` (the cell bound's floor). -/
theorem capS_hash (c : SymC) (wa : WilliamsAlgorithm) (hCDc : costCDH l (gate0 l F).alg c ≤ F.CD) (hcpsi : 1 ≤ F.E.cpsi)
    (hdA : dAH c (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) ≤ c.dA) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    2 ^ 32 * (PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) ^ 8 ≤ (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1 := by
  have hL1 := one_le_L n
  obtain ⟨hX8, hKS, hLS⟩ := S_facts (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) hL1
  have hAux := aux_le l F hcpsi kclk coef A a ha ha' Cs carriers translation hcall
  have hS := hbS_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hex := hcostH_exp n (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) F.CD c.dC c.dA c.eH c.eP c.dP (C1H l (gate0 l F).alg c) (cF1 l (gate0 l F).alg) (cW2 l) (cS l)
    (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) (c0F c) ((((gate0 l F).budget kclk coef A a ha).kOf n) + cF1 l (gate0 l F).alg * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (c.eH + c.eP) * (Nat.clog 2 (n + 2)) + c0F c) (2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cW2 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) (2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cS l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) hL1 hKS hLS hAux
    (by have : cF1 l (gate0 l F).alg * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ cF1 l (gate0 l F).alg * (8 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2))))) := Nat.mul_le_mul_left _ hX8
        have e : (1 + 8 * cF1 l (gate0 l F).alg) * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) = ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) + 8 * cF1 l (gate0 l F).alg * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) := by ring
        have e2 : cF1 l (gate0 l F).alg * (8 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2))))) = 8 * cF1 l (gate0 l F).alg * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) := by ring
        omega)
    (by have : cW2 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ cW2 l * (8 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2))))) := Nat.mul_le_mul_left _ hX8
        have e : (2 + 8 * cW2 l) * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) = 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) + 8 * cW2 l * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) := by ring
        have e2 : cW2 l * (8 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2))))) = 8 * cW2 l * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) := by ring
        omega)
    (by have : cS l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ cS l * (8 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2))))) := Nat.mul_le_mul_left _ hX8
        have e : (2 + 8 * cS l) * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) = 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) + 8 * cS l * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) := by ring
        have e2 : cS l * (8 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2))))) = 8 * cS l * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 2 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)) ^ 3) * (Nat.clog 2 (n + 2)) ^ 2 * ((((gate0 l F).budget kclk coef A a ha).kOf n) + (Nat.clog 2 (n + 2)))) := by ring
        omega)
    (by unfold costCDH hashB at hCDc; exact hCDc) (by unfold dAH at hdA; exact hdA)
  have h8 := hex.2.2.2.2.2.2.2
  have hS1 : PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 ≤ 2 ^ ((2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cS l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := (2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cS l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)))); omega
  show 2 ^ 32 * (PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) ^ 8 ≤ 2 ^ (n / 16 + c.dC * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))))
  calc 2 ^ 32 * (PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) ^ 8 ≤ 2 ^ 32 * 2 ^ (8 * ((2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cS l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) + 1)) :=
        Nat.mul_le_mul_left _ (pow_mono_mul 8 hS1)
    _ = 2 ^ (32 + 8 * ((2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cS l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) + 1)) := by rw [pow_add]
    _ ≤ 2 ^ (n / 16 + c.dC * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2)))) := Nat.pow_le_pow_right (by norm_num) h8

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr

end
