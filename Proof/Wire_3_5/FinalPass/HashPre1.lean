import Proof.Wire_3_5.FinalPass.HashRange
import Proof.Wire_3_5.FinalPass.HashRows

/-! # The HASH child request's precondition, part 1: the request's numbers at a THR call

alg:compiler (P3:1882-1900) at the HASH child request `hR R0 D p'` (the call's THR pool request `thrR0 … h Q' 0 m d pr 0`
with the printed HASH objective): with the HASH constants `hashK2 c` and the degree bound `d = d_D·β²`
(`hashDF`, the aux FILTER rows' degree `384·w_aux + 1 = O(L²)`, filt:soft P3:2253-2290), under the constraints
`HpreH`: the aux rows' degree is within `d`, the printed expression has at most `2^{k + c_V X²}` terms, `h·Q'·d ≤ pr`
and `|c|·2^{Q'} ≤ 2^{pr}` (the cleared weights `≤ Π_j W_j^{2t}·2^{2tℓ₀}`).

* `hashDF`, `cV`, `HpreH`; `walk_le`, **`lenV_le`**, **`hqd_hash`**, **`coef_hash`**.

Paper quantities of the main types: the HASH child request's `A`, `d`, `h·Q'·d` and coefficient widths. -/

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

/-- **The HASH requests' degree bound** `d = d_D·β²` (the aux FILTER rows' degree is `O(L²)`). -/
def hashDF (c : SymC) (x : FreeIn) : ℕ := c.dD * (β x * β x)

/-- The printed expression's term-count constant. -/
noncomputable def cV (l : Literals) : ℕ :=
  cN l + 24 * CallIndex.algX l + 66 + cJ l + 2 * cT l * cL0 l + 2 * cT l

/-- **The HASH constants' constraints read by `hpre`** (the literals' algorithm and constants alone). -/
structure HpreH (l : Literals) (alg : RepairRepresentation.DecompositionAlgorithm) (c : SymC) : Prop where
  dQ : 8 * eR l + 1 ≤ c.dQ
  dH : alg.coefficient * 4 ^ alg.degree + 2 ≤ c.dH
  eH : 26 * alg.degree + 1 ≤ c.eH
  dD : 4 * (192 * cE l + 385) ≤ c.dD
  dP1 : 3 * c.dH * c.dQ * c.dD ≤ c.dP
  eP1 : c.eH + 5 ≤ c.eP
  dP2 : 8 * cPW l + 8 * cT l * cL0 l + 3 * c.dQ ≤ c.dP

theorem L_le_n (n : ℕ) : Nat.clog 2 (n + 2) ≤ n + 1 :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := n + 1))

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The aux rows' degree is within `d`**. -/
theorem walk_le (c : SymC) (hdD : 4 * (192 * cE l + 385) ≤ c.dD) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    384 * (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 1 ≤ hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) := by
  have he := E_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL1 : 1 ≤ (Nat.clog 2 (n + 2)) := one_le_L n
  have hw : (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen = 2 * ((Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) / 4) + 1 := rfl
  have hd : hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) = c.dD * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) := rfl
  rw [hw, hd]
  have hX2 : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ 4 * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) := by
    have h2 : ((Nat.clog 2 (n + 2)) + 1) ≤ 2 * (Nat.clog 2 (n + 2)) := by omega
    calc (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ (2 * (Nat.clog 2 (n + 2))) * (2 * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul h2 h2
      _ = 4 * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) := by ring
  have hLL : 1 ≤ ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1 : 192 * (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 192 * cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have := Nat.mul_le_mul_left 192 he
    calc 192 * (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 192 * (cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := this
      _ = 192 * cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
  have h2 : 192 * cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ 192 * cE l * (4 * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2)))) := Nat.mul_le_mul_left _ hX2
  have h3 : 4 * (192 * cE l + 385) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ c.dD * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul_right _ hdD
  have e : 4 * (192 * cE l + 385) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) = 192 * cE l * (4 * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2)))) + 1540 * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) := by ring
  omega

/-- **The printed HASH expression has at most `2^{k + c_V X²}` terms** (at every prefix). -/
theorem lenV_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (plen pre : ℕ) :
    (PrimT.HashB.hashTermsM (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops plen pre).length ≤
      2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
  have hl := hashTermsM_length_le (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops plen pre
  have ht := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hnE := nE_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hA := A_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hJ := J_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hl0 := ell0_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have ht' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have hJ' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J = (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have hN : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 = 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) := by
    show (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) ^ 2 = _
    rw [← pow_mul, ← hkh, Nat.mul_comm]
  have hP : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops.length ≤ 2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) := by
    show (PrimT.C4H.hashPopsOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).length ≤ _
    rw [hashPops_length]; exact hA
  have hnE' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE ≤ 2 ^ (cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := hnE
  have hJ1 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J + 1 ≤ 2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1)) := by
    rw [hJ']; exact (Nat.add_le_add_right hJ 1).trans Nat.lt_two_pow_self
  have hlt : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 * (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t) ≤ 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    rw [ht']
    calc (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 * (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) * (2 * (cT l * ((Nat.clog 2 (n + 2)) + 1))) := Nat.mul_le_mul hl0 (by omega)
      _ = 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
  have hE1 : (2 ^ (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t) ≤ 2 ^ (2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) hlt
  have hE2 : 2 ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t) * 1 ≤ 2 ^ (2 * (cT l * ((Nat.clog 2 (n + 2)) + 1))) := by
    rw [Nat.mul_one, ht']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have key := Nat.mul_le_mul (le_of_eq hN) (Nat.mul_le_mul hnE' (Nat.mul_le_mul hP (Nat.mul_le_mul hJ1
    (Nat.mul_le_mul hE1 hE2))))
  refine hl.trans (key.trans ?_)
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
  have hXX : ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have i1 : (24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2 ≤ (24 * (CallIndex.algX l) + 66) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have h1 : (24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) ≤ (24 * (CallIndex.algX l) + 64) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ (by omega)
    have e : (24 * (CallIndex.algX l) + 66) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = (24 * (CallIndex.algX l) + 64) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 2 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
    omega
  have i2 : cJ l * ((Nat.clog 2 (n + 2)) + 1) ≤ cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXX
  have i3 : 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) ≤ 2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have : cT l * ((Nat.clog 2 (n + 2)) + 1) ≤ cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXX
    have e : 2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = 2 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by ring
    omega
  have e : cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (24 * (CallIndex.algX l) + 66) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) +
      2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by unfold cV; ring
  rw [e]
  omega

/-- **`h·Q'·d ≤ pr`** at the HASH request. -/
theorem hqd_hash (c : SymC) (hdP : 3 * c.dH * c.dQ * c.dD ≤ c.dP) (heP : c.eH + 5 ≤ c.eP) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 * (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 * hashDF c (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) ≤ (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 := by
  have hk : (((gate0 l F).budget kclk coef A a ha).kOf n) ≤ n := hcall.2.2.2.2.2.2.kq
  have hkh := kh_two l F kclk coef A a ha hs
  have hLn := L_le_n n
  show c.dH * (n + 1) ^ c.eH * (c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)))) * (c.dD * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2)))) ≤ c.dP * (n + 1) ^ c.eP
  have h1 : (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)) ≤ 3 * (n + 1) ^ 3 := by
    have a1 : (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (n + 1) ^ 3 := by
      calc (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (n + 1) * ((n + 1) * (n + 1)) := Nat.mul_le_mul hLn (Nat.mul_le_mul hLn hLn)
        _ = (n + 1) ^ 3 := by ring
    have a2 : (n + 1) ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have h2 : ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (n + 1) ^ 2 := by
    calc ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul hLn hLn
      _ = (n + 1) ^ 2 := by ring
  calc c.dH * (n + 1) ^ c.eH * (c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)))) * (c.dD * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))))
      ≤ c.dH * (n + 1) ^ c.eH * (c.dQ * (3 * (n + 1) ^ 3)) * (c.dD * (n + 1) ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)) (Nat.mul_le_mul_left _ h2)
    _ = 3 * c.dH * c.dQ * c.dD * (n + 1) ^ (c.eH + 5) := by ring
    _ ≤ c.dP * (n + 1) ^ c.eP := Nat.mul_le_mul hdP (Nat.pow_le_pow_right (by omega) heP)

/-- **`|c|·2^{Q'} ≤ 2^{pr}`** for every printed HASH term (at every prefix of at most `2tℓ₀` bits). -/
theorem coef_hash (c : SymC) (hdP : 8 * cPW l + 8 * cT l * cL0 l + 3 * c.dQ ≤ c.dP) (heP : 3 ≤ c.eP) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (plen pre : ℕ) (hplen : plen ≤ 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) :
    ∀ t ∈ PrimT.HashB.hashTermsM (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops plen pre,
      t.1.natAbs * 2 ^ ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) ≤ 2 ^ ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) := by
  intro t ht
  have hc := hashTerm_coef (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops plen pre hplen t ht
  have hW := prodW_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have htl := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hl0 := ell0_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have ht' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have hk : (((gate0 l F).budget kclk coef A a ha).kOf n) ≤ n := hcall.2.2.2.2.2.2.kq
  have hkh := kh_two l F kclk coef A a ha hs
  have hLn := L_le_n n
  have hlt : 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    rw [ht']
    calc 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ htl) hl0
      _ = 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
  have hQ : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 = c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) := rfl
  have hp : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 = c.dP * (n + 1) ^ c.eP := rfl
  rw [hQ, hp]
  have hc2 : t.1.natAbs ≤ 2 ^ (cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) * 2 ^ (2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) :=
    hc.trans (Nat.mul_le_mul hW (Nat.pow_le_pow_right (by norm_num) hlt))
  refine (Nat.mul_le_mul_right _ hc2).trans ?_
  rw [← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  have hXn : ((Nat.clog 2 (n + 2)) + 1) ≤ 2 * (n + 1) := by omega
  have hN3 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have a1 : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ 8 * (n + 1) ^ 3 := by
    calc (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ (2 * (n + 1)) * (2 * (n + 1)) * (2 * (n + 1)) := Nat.mul_le_mul (Nat.mul_le_mul hXn hXn) hXn
      _ = 8 * (n + 1) ^ 3 := by ring
  have a2 : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ 4 * (n + 1) ^ 3 := by
    have b1 : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ (2 * (n + 1)) * (2 * (n + 1)) := Nat.mul_le_mul hXn hXn
    have b2 : (n + 1) * (n + 1) ≤ (n + 1) ^ 3 := by
      calc (n + 1) * (n + 1) = (n + 1) ^ 2 := by ring
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have e : (2 * (n + 1)) * (2 * (n + 1)) = 4 * ((n + 1) * (n + 1)) := by ring
    omega
  have a3 : (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)) ≤ 3 * (n + 1) ^ 3 := by
    have b1 : (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (n + 1) ^ 3 := by
      calc (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (n + 1) * ((n + 1) * (n + 1)) := Nat.mul_le_mul hLn (Nat.mul_le_mul hLn hLn)
        _ = (n + 1) ^ 3 := by ring
    have b2 : (n + 1) ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have c1 : cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ cPW l * (8 * (n + 1) ^ 3) := Nat.mul_le_mul_left _ a1
  have c2 : 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ 2 * cT l * cL0 l * (4 * (n + 1) ^ 3) := Nat.mul_le_mul_left _ a2
  have c3 : c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) ≤ c.dQ * (3 * (n + 1) ^ 3) := Nat.mul_le_mul_left _ a3
  have c4 : (8 * cPW l + 8 * cT l * cL0 l + 3 * c.dQ) * (n + 1) ^ 3 ≤ c.dP * (n + 1) ^ c.eP :=
    Nat.mul_le_mul hdP (Nat.pow_le_pow_right (by omega) heP)
  have e1 : (8 * cPW l + 8 * cT l * cL0 l + 3 * c.dQ) * (n + 1) ^ 3 = cPW l * (8 * (n + 1) ^ 3) +
      2 * cT l * cL0 l * (4 * (n + 1) ^ 3) + c.dQ * (3 * (n + 1) ^ 3) := by ring
  omega

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
