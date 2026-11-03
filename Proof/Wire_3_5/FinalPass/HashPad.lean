import Lean
import Proof.Wire_3_5.FinalPass.HashPre1
import Proof.Wire_3_5.FinalPass.SymCost5Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashSz1
import Proof.Wire_3_5.FinalPass.HashSz2
import Proof.Wire_3_5.FinalPass.SymCost4
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.HashPadBase


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH stage's pad and its request's numbers (`HashEAt`'s `hR`, `Q' ≤ pr`, `1 ≤ h`)

P3:3098-3100 (the pad `2^ρ`, `ρ = max(n − 2k_h + d_Aβ, d_Rβ²)`) at a THR call's HASH stage: the HASH child family's
loop cell (cost `2K_ch + 2`, `K_ch = symKch = 2^{n − k + d_A L − 4}`, the comparison at the sum's width
`W = Q' + 2dRow + 2(pr+1) + 4` and the `s_h = 2t·ℓ₀` decisions, P3:2238-2251) fits the pad: the cell is
`4K_ch + 146W + 10s_h + 79`, `4K_ch = 2^{n−k+d_A L−2}`, and `146W + 10s_h + 79 ≤ c_Pad(n+1)^{e_P+3} ≤ 2^{n−k+d_A L−2}`
once `d_A ≥ e_P + 5 + ⌈log₂ c_Pad⌉` (fixed before `F`). Also `Q' ≤ pr` (from `h·Q'·d ≤ pr`) and `1 ≤ h`.

* `cPad`, **`padHR_hash`**, `hQp_hash`, `one_le_h_hash`.

Paper quantities of the main types: the HASH loop cell's steps against the pad `2^ρ`; the request's `Q' ≤ pr`. -/

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

/-- The pad's constant of the HASH loop cell's small terms. -/
noncomputable def cPad (l : Literals) (c : SymC) : ℕ := 146 * (3 * c.dQ + 2 * c.dP + 8) + 80 * cT l * cL0 l + 79

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The pad over the HASH family's cell** (`HashEAt`'s `hR` at the explicit cell cost). -/
theorem padHR_hash (c : SymC) (hdA : c.eP + 5 + Nat.clog 2 (cPad l c) ≤ c.dA) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (d : ℕ) :
    (2 * symKch l F c n + 2) + 1 + ((2 * symKch l F c n + 2) + 1 +
      (2 * PrimT.C4Loop.cmpCost ((ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) d ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0).P.Q + (2 * (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) d ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0).dRow + 2 * ((ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) d ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0).p + 1) + 4))
        (List.replicate (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) false) + 2)) + 1 ≤ 2 ^ ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6) := by
  have hL1 := one_le_L n
  have hkh := kh_two l F kclk coef A a ha hs
  have hk : (((gate0 l F).budget kclk coef A a ha).kOf n) ≤ n := hcall.2.2.2.2.2.2.kq
  have hLn := L_le_n n
  have htl := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hl0 := ell0_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have ht' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have hdr := two_dRow_le ((callInputs l F kclk coef A a ha).starParams n hs)
  have hK : (((gate0 l F).budget kclk coef A a ha).kOf n) = ((callInputs l F kclk coef A a ha).starParams n hs).r * ((callInputs l F kclk coef A a ha).starParams n hs).s := rfl
  have hrn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
  rw [← hK, hrn] at hdr
  -- the pad's exponent
  have hρ : n - (((gate0 l F).budget kclk coef A a ha).kOf n) + c.dA * (Nat.clog 2 (n + 2)) ≤ (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6 := by
    show _ ≤ max (n - ((SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) + c.dA * (Nat.clog 2 (n + 2))) (c.dR * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))))
    have : (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) = (((gate0 l F).budget kclk coef A a ha).kOf n) := by omega
    rw [this]
    exact le_max_left _ _
  have hK4 : symKch l F c n = 2 ^ (n - (((gate0 l F).budget kclk coef A a ha).kOf n) + c.dA * (Nat.clog 2 (n + 2)) - 4) := rfl
  -- the small terms
  have hQ : (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) d ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0).P.Q = c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) := rfl
  have hdR : (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) d ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0).dRow = PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) := rfl
  have hp : (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) d ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0).p = c.dP * (n + 1) ^ c.eP := rfl
  rw [cmpCost_eq, List.length_replicate, hK4, hQ, hdR, hp]
  have hN1 : 1 ≤ (n + 1) := by omega
  have hNe : ∀ j, j ≤ c.eP + 3 → (n + 1) ^ j ≤ (n + 1) ^ (c.eP + 3) := fun j hj => Nat.pow_le_pow_right hN1 hj
  have a1 : (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)) ≤ 3 * (n + 1) ^ (c.eP + 3) := by
    have b1 : (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (n + 1) ^ 3 := by
      calc (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (n + 1) * ((n + 1) * (n + 1)) := Nat.mul_le_mul hLn (Nat.mul_le_mul hLn hLn)
        _ = (n + 1) ^ 3 := by ring
    have b2 : (n + 1) ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have b3 := hNe 3 (by omega)
    omega
  have a2 : 2 * PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) ≤ 2 * (n + 1) ^ (c.eP + 3) := by
    have b1 : (n + 1) ≤ (n + 1) ^ (c.eP + 3) := Nat.le_self_pow (by omega) _
    omega
  have a3 : (n + 1) ^ c.eP ≤ (n + 1) ^ (c.eP + 3) := hNe c.eP (by omega)
  have a4 : (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) ≤ 8 * cT l * cL0 l * (n + 1) ^ (c.eP + 3) := by
    rw [ht']
    have b1 : 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ htl) hl0
    have b2 : ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) ≤ 4 * (n + 1) ^ (c.eP + 3) := by
      have c1 : ((Nat.clog 2 (n + 2)) + 1) ≤ 2 * (n + 1) := by omega
      have c2 : (n + 1) * (n + 1) ≤ (n + 1) ^ (c.eP + 3) := by
        calc (n + 1) * (n + 1) = (n + 1) ^ 2 := by ring
          _ ≤ _ := hNe 2 (by omega)
      have c3 : ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) ≤ (2 * (n + 1)) * (2 * (n + 1)) := Nat.mul_le_mul c1 c1
      have e : (2 * (n + 1)) * (2 * (n + 1)) = 4 * ((n + 1) * (n + 1)) := by ring
      omega
    have e1 : 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) = 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
    have b3 : 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ 2 * cT l * cL0 l * (4 * (n + 1) ^ (c.eP + 3)) := Nat.mul_le_mul_left _ b2
    have e2 : 2 * cT l * cL0 l * (4 * (n + 1) ^ (c.eP + 3)) = 8 * cT l * cL0 l * (n + 1) ^ (c.eP + 3) := by ring
    omega
  have hsmall : 146 * (c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) + (2 * PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) +
      2 * (c.dP * (n + 1) ^ c.eP + 1) + 4)) + 10 * (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) + 79 ≤ cPad l c * (n + 1) ^ (c.eP + 3) := by
    have b1 : c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) ≤ c.dQ * (3 * (n + 1) ^ (c.eP + 3)) := Nat.mul_le_mul_left _ a1
    have b2 : c.dP * (n + 1) ^ c.eP ≤ c.dP * (n + 1) ^ (c.eP + 3) := Nat.mul_le_mul_left _ a3
    have b3 : 1 ≤ (n + 1) ^ (c.eP + 3) := Nat.one_le_pow _ _ hN1
    have e : cPad l c * (n + 1) ^ (c.eP + 3) = 146 * (3 * (c.dQ * (n + 1) ^ (c.eP + 3))) + 292 * (c.dP * (n + 1) ^ (c.eP + 3)) +
        1168 * (n + 1) ^ (c.eP + 3) + 10 * (8 * cT l * cL0 l * (n + 1) ^ (c.eP + 3)) + 79 * (n + 1) ^ (c.eP + 3) := by
      unfold cPad; ring
    have e2 : c.dQ * (3 * (n + 1) ^ (c.eP + 3)) = 3 * (c.dQ * (n + 1) ^ (c.eP + 3)) := by ring
    omega
  have hpow : cPad l c * (n + 1) ^ (c.eP + 3) ≤ 2 ^ (Nat.clog 2 (cPad l c) + (c.eP + 3) * (Nat.clog 2 (n + 2))) := by
    have hc2 : cPad l c ≤ 2 ^ Nat.clog 2 (cPad l c) := Nat.le_pow_clog (by norm_num) (cPad l c)
    have hn2 : (n + 1) ^ (c.eP + 3) ≤ 2 ^ ((c.eP + 3) * (Nat.clog 2 (n + 2))) := pow_mono_mul (c.eP + 3) (n1_le_L n)
    calc cPad l c * (n + 1) ^ (c.eP + 3) ≤ 2 ^ Nat.clog 2 (cPad l c) * 2 ^ ((c.eP + 3) * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul hc2 hn2
      _ = 2 ^ (Nat.clog 2 (cPad l c) + (c.eP + 3) * (Nat.clog 2 (n + 2))) := (pow_add 2 _ _).symm
  obtain ⟨E, hE⟩ : ∃ E, E = n - (((gate0 l F).budget kclk coef A a ha).kOf n) + c.dA * (Nat.clog 2 (n + 2)) := ⟨_, rfl⟩
  rw [← hE] at hρ ⊢
  have hEL : Nat.clog 2 (cPad l c) + (c.eP + 3) * (Nat.clog 2 (n + 2)) + 2 ≤ E := by
    have b1 : (c.eP + 5 + Nat.clog 2 (cPad l c)) * (Nat.clog 2 (n + 2)) ≤ c.dA * (Nat.clog 2 (n + 2)) := Nat.mul_le_mul_right _ hdA
    have b2 : Nat.clog 2 (cPad l c) + 2 ≤ (Nat.clog 2 (cPad l c) + 2) * (Nat.clog 2 (n + 2)) := Nat.le_mul_of_pos_right _ hL1
    have e : (c.eP + 5 + Nat.clog 2 (cPad l c)) * (Nat.clog 2 (n + 2)) = (c.eP + 3) * (Nat.clog 2 (n + 2)) + (Nat.clog 2 (cPad l c) + 2) * (Nat.clog 2 (n + 2)) := by ring
    omega
  have hE4 : 4 ≤ E := by
    have : c.eP + 3 ≤ (c.eP + 3) * (Nat.clog 2 (n + 2)) := Nat.le_mul_of_pos_right _ hL1
    omega
  have e4 : (2 : ℕ) ^ (E - 2) = 4 * 2 ^ (E - 4) := by
    rw [show E - 2 = (E - 4) + 2 by omega, pow_add]; ring
  have e2 : (2 : ℕ) ^ E = 4 * 2 ^ (E - 2) := by
    have h : (2 : ℕ) ^ E = 2 ^ ((E - 2) + 2) := congrArg (2 ^ ·) (by omega)
    rw [h, pow_add]; ring
  have hsm2 : (2 : ℕ) ^ (Nat.clog 2 (cPad l c) + (c.eP + 3) * (Nat.clog 2 (n + 2))) ≤ 2 ^ (E - 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpad : (2 : ℕ) ^ E ≤ 2 ^ ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6) := Nat.pow_le_pow_right (by norm_num) hρ
  generalize (2 : ℕ) ^ (Nat.clog 2 (cPad l c) + (c.eP + 3) * (Nat.clog 2 (n + 2))) = Y at hpow hsm2
  generalize cPad l c * (n + 1) ^ (c.eP + 3) = Z at hsmall hpow
  generalize (2 : ℕ) ^ ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6) = P at hpad
  generalize (2 : ℕ) ^ (E - 4) = A4 at e4 ⊢
  generalize (2 : ℕ) ^ (E - 2) = A2 at e4 e2 hsm2
  generalize (2 : ℕ) ^ E = A0 at e2 hpad
  omega

/-- **`Q' ≤ pr`** at the HASH request (from `h·Q'·d ≤ pr`, `h, d ≥ 1`). -/
theorem hQp_hash (c : SymC) (hdH : 1 ≤ c.dH) (hdD : 1 ≤ c.dD) (hdP : 3 * c.dH * c.dQ * c.dD ≤ c.dP)
    (heP : c.eH + 5 ≤ c.eP) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 ≤ (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 := by
  have h := hqd_hash l F c hdP heP kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL1 := one_le_L n
  have h1 : 1 ≤ (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 := by
    show 1 ≤ c.dH * (n + 1) ^ c.eH
    exact Nat.mul_le_mul hdH (Nat.one_le_pow _ _ (by omega))
  have h2 : 1 ≤ hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) := by
    show 1 ≤ c.dD * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2)))
    exact Nat.mul_le_mul hdD (Nat.mul_le_mul hL1 hL1)
  calc (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 = 1 * (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 * 1 := by ring
    _ ≤ (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 * (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 * hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) := Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) h2
    _ ≤ _ := h

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr

end
