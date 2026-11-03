import Lean
import Proof.Wire_3_5.FinalPass.HashPre1
import Proof.Wire_3_5.FinalPass.HashOcc
import Proof.Wire_3_5.Primitive.Writers.ThrSide6
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashRange
import Proof.Wire_3_5.FinalPass.HashSz1
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.HashOccBase
import Proof.Wire_3_5.FinalPass.HashPre1Base
import Proof.Wire_3_5.Primitive.Writers.ThrSide6Base


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH child request's precondition, part 2: the printer's budget and `hpre`

alg:eq-budget (P3:1897-1900) at the HASH child request, against the auxiliary load
`Ψ_aux = C_D[k + L² + (k+L³)L²(k+L)]` (P3:3101-3102, "It suffices that `max{Ψ_i, Ψ_aux} ≤ c₀(n−k)`", P3:3106-3107):
the printed expression has `≤ 2^{k + c_V X²}` terms, the dense pool `≤ 2^{k + c_{Da} L}` children (the `thrD_le`),
`m = 2t + 1`, `Q' = d_Q(L³ + k + L)`, `d = d_D L²`, so `log A + m + Q' + Q'd·log(P_ex+1) ≤ C₁·Ψ_aux/C_D`, within
`dRow ≥ (n−k)/2` once `C_D ≥ 160C₁ + 2` (`occCDH`, fixed before `F`). With the pool's fits at `h = d_H(n+1)^{e_H}`
(the `thr_fits_of`) and part 1's numbers: **`hpre_hash`**, `C3Req.Pre` of the HASH child request at every prefix of
at most `s_h = 2t·ℓ₀` bits (`HashEAt`'s `hpre`).

* **`fits_hash`**, **`occ_hash`**, **`hpre_hash`**.

Paper quantities of the main types: alg:compiler's precondition and alg:eq-budget at the HASH child request. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

section Gate
variable (l : Literals) (F : GateFree l)
/-- **The pool fits at the HASH `h`** (the `thr_fits_of` at `h = d_H(n+1)^{e_H}`). -/
theorem fits_hash (c : SymC) (hdH : (gate0 l F).alg.coefficient * 4 ^ (gate0 l F).alg.degree + 2 ≤ c.dH)
    (heH : 26 * (gate0 l F).alg.degree + 1 ≤ c.eH) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Q psi : ℕ) :
    CompilerMachine.Pool.CoefFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
        (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) Q psi) ∧
      CompilerMachine.Req.PNFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
        (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) Q psi) ∧
      CompilerMachine.Req.DenseFit ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) (CompilerMachine.Pool.densePool (gate0 l F).alg
        (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
          (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) Q psi).gates
        (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs)) (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))) := by
  have hcar : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hb := symBud_le (gate0 l F).alg n
  refine PrimAsm.ThrSide.thr_fits_of (gate0 l F).alg ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers hcar hd _ Q psi ?_
  show symBud (gate0 l F).alg n + n + 2 ≤ c.dH * (n + 1) ^ c.eH
  exact hb.trans (Nat.mul_le_mul hdH (Nat.pow_le_pow_right (by omega) heH))

/-- **The HASH printer's budget** (alg:eq-budget) at every prefix, against `Ψ_aux`. -/
theorem occ_hash (c : SymC) (hCD : occCDH l (gate0 l F).alg c ≤ F.CD) (hcpsi : 1 ≤ F.E.cpsi) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (p' : List Bool) :
    (2 * (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').occBound (gate0 l F).alg) * (2 * (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').occBound (gate0 l F).alg) ≤
      SourceInterfaces.rectangularInnerDimension (2 ^ (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').dRow) := by
  have hV := lenV_le l F kclk coef A a ha ha' Cs carriers translation hcall hs p'.length (SeedFix.listNum p')
  have hD := PrimAsm.ThrSide.thrD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
  refine SampShape.occ_of (gate0 l F).alg (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p') ((((gate0 l F).budget kclk coef A a ha).kOf n) + cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) ((((gate0 l F).budget kclk coef A a ha).kOf n) + cDa (gate0 l F).alg * (Nat.clog 2 (n + 2))) hV hD ?_
  have hm : (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').m = 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 := m_hash l F c kclk coef A a ha Cs carriers hs
  have hQ : (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').P.Q = c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) := rfl
  have hd : (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').d = c.dD * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) := rfl
  have hdRow : (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p').dRow = PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) := rfl
  rw [hm, hQ, hd, hdRow]
  have ht := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hfits := hcall.2.2.2.2.2.2.pre
  have hdr : n - (((gate0 l F).budget kclk coef A a ha).kOf n) ≤ 2 * PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) := two_dRow_ge ((callInputs l F kclk coef A a ha).starParams n hs)
  have hL1 := one_le_L n
  have hψ : ((gate0 l F).budget kclk coef A a ha).psiOf n = loadPsi F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n)
      (((gate0 l F).budget kclk coef A a ha).capOf .sym n) := rfl
  have hAux : loadAux F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) ≤ ((gate0 l F).budget kclk coef A a ha).psiOf n := by
    rw [hψ]; unfold loadPsi; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hcp : 1 ≤ (gate0 l F).E.cpsi := hcpsi
  have hn : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤ n := by
    have : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤
        (gate0 l F).E.cpsi * ((gate0 l F).budget kclk coef A a ha).psiOf n := Nat.le_mul_of_pos_left _ hcp
    exact this.trans (le_trans (Nat.le_add_right _ _) hfits)
  obtain ⟨K, hKd⟩ : ∃ K, K = (((gate0 l F).budget kclk coef A a ha).kOf n) := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = (Nat.clog 2 (n + 2)) := ⟨_, rfl⟩
  obtain ⟨ψ, hψd⟩ : ∃ ψ, ψ = ((gate0 l F).budget kclk coef A a ha).psiOf n := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T, T = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := ⟨_, rfl⟩
  obtain ⟨kh, hkhd⟩ : ∃ kh, kh = (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) := ⟨_, rfl⟩
  obtain ⟨dR, hdRd⟩ : ∃ dR, dR = PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  rw [← hKd, ← hLd, ← hTd, ← hkhd, ← hdRd]
  rw [← hLd, ← hTd] at ht
  rw [← hkhd, ← hKd] at hkh
  rw [← hKd, ← hdRd] at hdr
  rw [← hKd, ← hLd, ← hψd] at hAux
  rw [← hψd] at hn
  rw [← hLd] at hL1
  have hAuxE : loadAux F.CD K L = F.CD * (K + L ^ 2 + (K + L ^ 3) * L ^ 2 * (K + L)) := rfl
  rw [hAuxE] at hAux
  obtain ⟨S, hSd⟩ : ∃ S, S = K + L ^ 2 + (K + L ^ 3) * L ^ 2 * (K + L) := ⟨_, rfl⟩
  rw [← hSd] at hAux
  have hCD2 : 2 ≤ F.CD := by unfold occCDH at hCD; omega
  have hC1 : 160 * C1H l (gate0 l F).alg c ≤ F.CD := by unfold occCDH at hCD; omega
  -- the pieces against `S`
  have hL2 : L * L = L ^ 2 := by ring
  have hL3 : L * (L * L) = L ^ 3 := by ring
  have hLL1 : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hLL : L ≤ L ^ 2 := Nat.le_self_pow (by norm_num) _
  have hL3le : L ≤ L ^ 3 := Nat.le_self_pow (by norm_num) _
  have hPS : (K + L ^ 3) * L ^ 2 * (K + L) ≤ S := by rw [hSd]; omega
  have hL3S : L ^ 3 ≤ S := by
    have h1 : L ^ 3 ≤ (K + L ^ 3) * L ^ 2 * (K + L) := by
      calc L ^ 3 = L ^ 3 * 1 * 1 := by ring
        _ ≤ (K + L ^ 3) * L ^ 2 * (K + L) := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hLL1) (by omega)
    omega
  have hKS : K ≤ S := by rw [hSd]; omega
  have hL2S : L ^ 2 ≤ S := by rw [hSd]; omega
  have hS1 : 1 ≤ S := by omega
  have p1 : cV l * ((L + 1) * (L + 1)) ≤ 4 * cV l * S := by
    have h1 : (L + 1) * (L + 1) ≤ 4 * L ^ 2 := by
      have h2 : L + 1 ≤ 2 * L := by omega
      calc (L + 1) * (L + 1) ≤ (2 * L) * (2 * L) := Nat.mul_le_mul h2 h2
        _ = 4 * L ^ 2 := by ring
    calc cV l * ((L + 1) * (L + 1)) ≤ cV l * (4 * L ^ 2) := Nat.mul_le_mul_left _ h1
      _ ≤ cV l * (4 * S) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * cV l * S := by ring
  have p2 : 2 * T + 1 ≤ (4 * cT l + 1) * S := by
    have h1 : T ≤ cT l * (2 * L) := ht.trans (Nat.mul_le_mul_left _ (by omega))
    have h2 : cT l * (2 * L) ≤ cT l * (2 * S) := Nat.mul_le_mul_left _ (by omega)
    have e : (4 * cT l + 1) * S = 2 * (cT l * (2 * S)) + S := by ring
    omega
  have p3 : c.dQ * (L * (L * L) + kh + kh + L) ≤ 3 * c.dQ * S := by
    have h1 : L * (L * L) + kh + kh + L ≤ 3 * S := by rw [hL3]; omega
    calc c.dQ * (L * (L * L) + kh + kh + L) ≤ c.dQ * (3 * S) := Nat.mul_le_mul_left _ h1
      _ = 3 * c.dQ * S := by ring
  have p4 : c.dQ * (L * (L * L) + kh + kh + L) * (c.dD * (L * L)) * (K + cDa (gate0 l F).alg * L) ≤
      2 * c.dQ * c.dD * (cDa (gate0 l F).alg + 1) * S := by
    have h1 : L * (L * L) + kh + kh + L ≤ 2 * (K + L ^ 3) := by rw [hL3]; omega
    have h2 : K + cDa (gate0 l F).alg * L ≤ (cDa (gate0 l F).alg + 1) * (K + L) := by
      have e : (cDa (gate0 l F).alg + 1) * (K + L) = cDa (gate0 l F).alg * K + K + cDa (gate0 l F).alg * L + L := by ring
      omega
    calc c.dQ * (L * (L * L) + kh + kh + L) * (c.dD * (L * L)) * (K + cDa (gate0 l F).alg * L)
        ≤ c.dQ * (2 * (K + L ^ 3)) * (c.dD * (L * L)) * ((cDa (gate0 l F).alg + 1) * (K + L)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) le_rfl) h2
      _ = 2 * c.dQ * c.dD * (cDa (gate0 l F).alg + 1) * ((K + L ^ 3) * L ^ 2 * (K + L)) := by ring
      _ ≤ 2 * c.dQ * c.dD * (cDa (gate0 l F).alg + 1) * S := Nat.mul_le_mul_left _ hPS
  have hX : K + cV l * ((L + 1) * (L + 1)) + (2 * T + 1) + c.dQ * (L * (L * L) + kh + kh + L) +
      c.dQ * (L * (L * L) + kh + kh + L) * (c.dD * (L * L)) * (K + cDa (gate0 l F).alg * L) + 1 ≤ C1H l (gate0 l F).alg c * S := by
    have e : C1H l (gate0 l F).alg c * S = 4 * cV l * S + (4 * cT l + 1) * S + 3 * c.dQ * S +
        2 * c.dQ * c.dD * (cDa (gate0 l F).alg + 1) * S + 2 * S := by unfold C1H; ring
    omega
  have hA : F.CD * (K + cV l * ((L + 1) * (L + 1)) + (2 * T + 1) + c.dQ * (L * (L * L) + kh + kh + L) +
      c.dQ * (L * (L * L) + kh + kh + L) * (c.dD * (L * L)) * (K + cDa (gate0 l F).alg * L) + 1) ≤ C1H l (gate0 l F).alg c * ψ := by
    calc _ ≤ F.CD * (C1H l (gate0 l F).alg c * S) := Nat.mul_le_mul_left _ hX
      _ = C1H l (gate0 l F).alg c * (F.CD * S) := by ring
      _ ≤ C1H l (gate0 l F).alg c * ψ := Nat.mul_le_mul_left _ hAux
  have hk : 2 * K ≤ ψ := by
    have h1 : 2 * K ≤ F.CD * K := Nat.mul_le_mul_right _ hCD2
    have h2 : F.CD * K ≤ F.CD * S := Nat.mul_le_mul_left _ hKS
    omega
  have h := occ_num ψ n K dR F.CD (K + cV l * ((L + 1) * (L + 1)) + (2 * T + 1) + c.dQ * (L * (L * L) + kh + kh + L) +
      c.dQ * (L * (L * L) + kh + kh + L) * (c.dD * (L * L)) * (K + cDa (gate0 l F).alg * L)) 0 (C1H l (gate0 l F).alg c) 0 (by omega) hA
    (by simp) hC1 (by simp) hn hk hdr
  rw [Nat.add_zero] at h
  exact h

/-- **`HashEAt`'s `hpre`**: `C3Req.Pre` of the HASH child request at every prefix of at most `s_h = 2tℓ₀` bits. -/
theorem hpre_hash (c : SymC) (hc : HpreH l (gate0 l F).alg c) (hCD : occCDH l (gate0 l F).alg c ≤ F.CD) (hcpsi : 1 ≤ F.E.cpsi) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ∀ (p : List Bool) (b : Bool), p.length < 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 → (PrimT.C4H.hR (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) (hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (p ++ [b])).Pre (gate0 l F).alg := by
  intro p b hp
  have hplen : (p ++ [b]).length ≤ 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 := by
    rw [List.length_append, List.length_singleton]; omega
  have hfits := fits_hash l F c hc.dH hc.eH kclk coef A a ha ha' Cs carriers translation hcall hs ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
  have hm := m_hash l F c kclk coef A a ha Cs carriers hs
  have hL1 := one_le_L n
  have hdQ : 1 ≤ c.dQ := by have := hc.dQ; omega
  have hG : 2 * (carriers.map List.length).sum ≤ (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length := by rw [pool_length]; omega
  have hFs : ∀ i, PrimAsm.BShape.PolyOk (384 * (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 1) (4 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G) ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs.getD i []) :=
    hashFs_getD ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) (PrimAsm.WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (PrimAsm.WriterIface.auxEnum (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length n hG
  have hpop : ∀ pop ∈ (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops, ∀ gi ∈ pop.2, gi < (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G := fun pop hpop =>
    (mem_hashPops (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers pop hpop).2
  have hw1 : 1 ≤ (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen := by
    show 1 ≤ 2 * ((Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) / 4) + 1
    omega
  have hfl : (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length = 4 * (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) * 2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) := by
    simp [PrimT.C4Geo.flips]
  refine ⟨C3Geo.poolReq_pre _ _ _ _ _ _, ?_, ?_, ?_, ?_, hfits.2.1, hfits.2.2,
    hqd_hash l F c hc.dP1 hc.eP1 kclk coef A a ha ha' Cs carriers translation hcall hs,
    coef_hash l F c hc.dP2 (by have := hc.eP1; omega) kclk coef A a ha ha' Cs carriers translation hcall hs (p ++ [b]).length (SeedFix.listNum (p ++ [b])) hplen,
    C3Geo.width_le_dRow _, PrimT.C4Geo.cols_length _, C3Geo.cols_lt _,
    occ_hash l F c hCD hcpsi kclk coef A a ha ha' Cs carriers translation hcall hs (p ++ [b])⟩
  · show 1 ≤ (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4
    rw [hm]; omega
  · show 1 ≤ c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)))
    have h1 : 1 ≤ (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)) := by omega
    exact le_trans h1 (Nat.le_mul_of_pos_left _ hdQ)
  · intro t ht
    show t.2.length = (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4
    rw [hm, PrimT.HashB.hashTermsM_uniform _ _ _ _ _ _ _ _ t ht]
    show 1 + 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) = 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1
    omega
  · intro t ht f hf mono hmono
    have hok := hashFactor_ok (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops (p ++ [b]).length
      (SeedFix.listNum (p ++ [b])) (384 * (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 1) (4 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G) (by omega) le_rfl hFs hpop
      t ht f hf mono hmono
    refine ⟨hok.1.trans (walk_le l F c hc.dD kclk coef A a ha ha' Cs carriers translation hcall hs), fun x hx => lt_of_lt_of_le (hok.2 x hx) ?_⟩
    show 4 * (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) ^ 2 * (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length *
      ((PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).map PrimT.C4Geo.suppG).length
    rw [hfl, List.length_map]
    exact le_of_eq (by ring)

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr

end
