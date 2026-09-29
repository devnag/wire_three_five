import Proof.Wire_3_5.FinalPass.FreeGenH2
import Proof.Wire_3_5.FinalPass.HashFree
import Proof.Wire_3_5.FinalPass.HashPops
import Proof.Wire_3_5.FinalPass.HashSz2

/-! # The HASH call's recovery range (`HashEAt`'s range clause)

filt:aux-precision (P3:2291-2296): "`Q_aux > log₂Δ₀ + k + s_aux + log₂(H_max+1)`, `Q_aux = O_D(k + L³)`". At a THR call's
HASH stage with the HASH constants `hashK2 c` (`m = 2t + 1`, `Q' = d_Q(β³ + 2k_h + β)`), the printed objective at every
prefix of at most `2t·ℓ₀` bits is nonnegative and `2^{m−1}·V < 2^{Q'}` once `d_Q ≥ 8e_R + 1`: the value is at most
`N²·n_E·|pops|·2^{2tℓ₀}·Π_j W_j^{2t}·(M + J(3M)^{2t}) ≤ 2^{k + e_R X³ − 2t}` (`HashSz1`, `HashSz2`, `HashPops`).

* `hashK2`, `eR`, `m_hash`, `Q_hash`, `mj_le`, **`bnd_le`**, **`hrange_hash`**.

Paper quantities of the main types: the HASH recovery precision `Q'` against the printed column value. -/

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

/-- **The HASH constants** on the SYM record: `m = 2·a + 1` (the arity slot holds `t`), no floor. -/
def hashK2 (c : SymC) : FreeK2 := ⟨⟨c.dT, c.dC, c.dQ, c.dH, 0, 0, 0, 2, 1, 0, c.dP, c.dA, c.dR⟩, c.eH, c.eP, 0⟩

/-- The range's exponent constant. -/
noncomputable def eR (l : Literals) : ℕ :=
  2 * cT l + cN l + 24 * CallIndex.algX l + 67 + 2 * cT l * cL0 l + cPW l + cJ l + 60 * cT l

section Gate
variable (l : Literals) (F : GateFree l)

theorem m_hash (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4 = 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 := by
  show max (0 * carriers.length + 0 * ((Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * W (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) + 0 * W (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) + 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 0 * _ + 1) 0 = _
  simp

theorem Q_hash (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 = c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) := rfl

/-- `M + J(3M)^{2t} ≤ 2^{1 + c_J X + 60 c_T X²}`. -/
theorem mj_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.M + (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J * (3 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.M) ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t)) ≤ 2 ^ (1 + cJ l * ((Nat.clog 2 (n + 2)) + 1) + 60 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)))) := by
  have hM := M_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hJ := J_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have ht := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hM' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.M = (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) := rfl
  have hJ' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J = (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have ht' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  rw [hM', hJ', ht']
  have hJ2 : (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1)) := hJ.trans (Nat.lt_two_pow_self).le
  have h3M : 3 * (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ≤ 2 ^ (2 + 28 * ((Nat.clog 2 (n + 2)) + 1)) := by rw [pow_add]; omega
  have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
  have hXX : ((Nat.clog 2 (n + 2)) + 1) ≤ ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have he : (2 + 28 * ((Nat.clog 2 (n + 2)) + 1)) * (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ 60 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
    have h1 : (2 + 28 * ((Nat.clog 2 (n + 2)) + 1)) * (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ (2 + 28 * ((Nat.clog 2 (n + 2)) + 1)) * (2 * (cT l * ((Nat.clog 2 (n + 2)) + 1))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ht)
    have h2 : cT l * ((Nat.clog 2 (n + 2)) + 1) ≤ cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXX
    have e : (2 + 28 * ((Nat.clog 2 (n + 2)) + 1)) * (2 * (cT l * ((Nat.clog 2 (n + 2)) + 1))) = 4 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) + 56 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by ring
    omega
  have hp : (3 * (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs)) ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ 2 ^ (60 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)))) :=
    (Nat.pow_le_pow_left h3M _).trans ((le_of_eq (pow_mul 2 (2 + 28 * ((Nat.clog 2 (n + 2)) + 1)) (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))).symm).trans
      (Nat.pow_le_pow_right (by norm_num) he))
  have hJp : (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (3 * (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs)) ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ 2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1) + 60 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)))) := by
    rw [pow_add]; exact Nat.mul_le_mul hJ2 hp
  have hcJ : 28 ≤ cJ l := by unfold cJ; omega
  have hM2 : (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ≤ 2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1) + 60 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)))) :=
    hM.trans (Nat.pow_le_pow_right (by norm_num) (by
      have : 28 * ((Nat.clog 2 (n + 2)) + 1) ≤ cJ l * ((Nat.clog 2 (n + 2)) + 1) := Nat.mul_le_mul_right _ hcJ
      omega))
  rw [show 1 + cJ l * ((Nat.clog 2 (n + 2)) + 1) + 60 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) = (cJ l * ((Nat.clog 2 (n + 2)) + 1) + 60 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)))) + 1 by ring,
    pow_succ]
  omega

/-- **The printed value's bound, with the scale `2^{m−1}`**: `≤ 2^{k + e_R X³}`. -/
theorem bnd_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    2 ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) * ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 * ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops.length) *
      (2 ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) * (SeedFix.prodW (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP * ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.M + (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J * (3 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.M) ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t))))) ≤ 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + eR l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
  have ht := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hnE := nE_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hA := A_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hl0 := ell0_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hW := prodW_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hmj := mj_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have ht' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have hN : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 = 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) := by
    show (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) ^ 2 = _
    rw [← pow_mul, ← hkh, Nat.mul_comm]
  have hP : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops.length ≤ 2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) := by
    show (PrimT.C4H.hashPopsOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).length ≤ _
    rw [hashPops_length]; exact hA
  have hnE' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE ≤ 2 ^ (cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := hnE
  have hT2 : 2 ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ 2 ^ (2 * (cT l * ((Nat.clog 2 (n + 2)) + 1))) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hTL : 2 ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) ≤ 2 ^ (2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1))) := by
    rw [ht']
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul (by omega) hl0)
  have key := Nat.mul_le_mul hT2 (Nat.mul_le_mul (Nat.mul_le_mul (le_of_eq hN) (Nat.mul_le_mul hnE' hP))
    (Nat.mul_le_mul hTL (Nat.mul_le_mul hW hmj)))
  refine key.trans ?_
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
  have hXX : ((Nat.clog 2 (n + 2)) + 1) ≤ ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hXXX : ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_right _ (by omega)
  have i1 : 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) ≤ 2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have : cT l * ((Nat.clog 2 (n + 2)) + 1) ≤ cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ (hXX.trans hXXX)
    have e : 2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = 2 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by ring
    omega
  have i2 : cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXXX
  have i3 : (24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2 ≤ (24 * (CallIndex.algX l) + 66) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have h1 : (24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) ≤ (24 * (CallIndex.algX l) + 64) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) :=
      Nat.mul_le_mul_left _ ((show (Nat.clog 2 (n + 2)) ≤ ((Nat.clog 2 (n + 2)) + 1) by omega).trans (hXX.trans hXXX))
    have e : (24 * (CallIndex.algX l) + 66) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = (24 * (CallIndex.algX l) + 64) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 2 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
    omega
  have i4 : 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) ≤ 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have e : 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) = 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
    rw [e]; exact Nat.mul_le_mul_left _ hXXX
  have i5 : 1 + cJ l * ((Nat.clog 2 (n + 2)) + 1) + 60 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) ≤ (1 + cJ l + 60 * cT l) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have h1 : cJ l * ((Nat.clog 2 (n + 2)) + 1) ≤ cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ (hXX.trans hXXX)
    have h2 : cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXXX
    have e : (1 + cJ l + 60 * cT l) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 60 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by ring
    omega
  have e : (((gate0 l F).budget kclk coef A a ha).kOf n) + eR l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = (((gate0 l F).budget kclk coef A a ha).kOf n) + (2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (24 * (CallIndex.algX l) + 66) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) +
      2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (1 + cJ l + 60 * cT l) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
    unfold eR; ring
  rw [e]
  omega

/-- **The HASH recovery range** (`HashEAt`'s range clause) once `d_Q ≥ 8e_R + 1`. -/
theorem hrange_hash (c : SymC) (hdQ : 8 * eR l + 1 ≤ c.dQ) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (h d pr : ℕ) :
    ∀ p' : List Bool, p'.length ≤ 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 → ∀ ρ : ℕ → Bool,
      0 ≤ Shared.IntExpression.eval (PrimT.C4H.hV (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p') ρ ∧
        (2 : ℤ) ^ ((ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation h ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) d pr 0).m - 1) * Shared.IntExpression.eval (PrimT.C4H.hV (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p') ρ <
          2 ^ (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation h ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) d pr 0).P.Q := by
  intro p' hp ρ
  have ht1 := t_pos l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL : ∀ pop ∈ (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops, pop.2.length ≤ (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.M := fun pop hpop =>
    (mem_hashPops (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers pop hpop).1
  obtain ⟨h0, h1⟩ := hashTermsM_range (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops p'.length (SeedFix.listNum p') ρ
    ht1 hp hL
  refine ⟨h0, ?_⟩
  have hm : (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation h ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) d pr 0).m - 1 = 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := by
    show (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4 - 1 = _
    rw [m_hash l F c kclk coef A a ha Cs carriers hs]; omega
  have hQ : (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation h ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0 ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) d pr 0).P.Q = c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) :=
    Q_hash l F c kclk coef A a ha Cs carriers hs
  rw [hm, hQ]
  have hb := bnd_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  obtain ⟨Bn, hBn⟩ : ∃ Bn : ℕ, Bn = (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 * ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops.length) *
      (2 ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) * (SeedFix.prodW (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP * ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.M + (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J * (3 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.M) ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t)))) := ⟨_, rfl⟩
  rw [← hBn] at hb
  have hcast : ((((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 * ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops.length) : ℕ) : ℤ) *
      (2 ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) * ((SeedFix.prodW (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP : ℤ) * ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.M + (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J * (3 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.M) ^
        (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t))))) = (Bn : ℤ) := by rw [hBn]; push_cast; ring
  rw [hcast] at h1
  -- the exponent
  have hkh := kh_two l F kclk coef A a ha hs
  have hL1 : 1 ≤ (Nat.clog 2 (n + 2)) := one_le_L n
  have hX8 : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ 8 * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2)))) := by
    have h2 : ((Nat.clog 2 (n + 2)) + 1) ≤ 2 * (Nat.clog 2 (n + 2)) := by omega
    calc (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ (2 * (Nat.clog 2 (n + 2))) * (2 * (Nat.clog 2 (n + 2))) * (2 * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul (Nat.mul_le_mul h2 h2) h2
      _ = 8 * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2)))) := by ring
  have hlt : (((gate0 l F).budget kclk coef A a ha).kOf n) + eR l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) < c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) := by
    have h3 : eR l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ eR l * (8 * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))))) := Nat.mul_le_mul_left _ hX8
    have h4 : (8 * eR l + 1) * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) ≤
        c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) := Nat.mul_le_mul_right _ hdQ
    have e : (8 * eR l + 1) * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) = eR l * (8 * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))))) +
        (8 * eR l * ((SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) + (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) := by ring
    omega
  have hfin : 2 ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) * Bn < 2 ^ (c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)))) :=
    lt_of_le_of_lt hb (Nat.pow_lt_pow_right (by norm_num) hlt)
  have hfinZ : ((2 ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) * Bn : ℕ) : ℤ) < ((2 ^ (c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)))) : ℕ) : ℤ) :=
    by exact_mod_cast hfin
  push_cast at hfinZ
  have hpos : (0 : ℤ) ≤ 2 ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) := by positivity
  calc (2 : ℤ) ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) * Shared.IntExpression.eval (PrimT.C4H.hV (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p') ρ ≤ 2 ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) * (Bn : ℤ) :=
        mul_le_mul_of_nonneg_left h1 hpos
    _ < _ := hfinZ

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
