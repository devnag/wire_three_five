import Lean
import Proof.Wire_3_5.FinalPass.HashPre1
import Proof.Wire_3_5.Primitive.SeedFix.C4HB
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashSz1
import Proof.Wire_3_5.FinalPass.HashSz2
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.HashSBase


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH printer's size `hbS` at a THR call, F-free (the C4HB)

`filt:soft` P3:2253-2290 ("each printed term has fixed arity and at most `poly(M,2^{O(k)})` integer size") and
filt:aux-precision P3:2291-2296: the Hb size `hbS D` (the cell count `2^{2t+2tℓ₀}(J+1)|pops|n_E N²`, `2^{2t+2tℓ₀}`,
`2^{ℓ₀+1}`, the HASH tape's word, the populations' and weights' streams, `G`, `N²`, `n_E`) at every THR call is at most
`2^{2k + c_S X³}` (`X = ⌈log₂(n+2)⌉ + 1`), with `c_S` of the literals only: the HASH rows have `(8Σ|X_j|+1)^{384w+1}`
monomials, `w = O(L²)`, so the tape's word has `2^{2k + O(L³)}` bits (unary atom codes below `4N²G`); the weights'
stream is `(J+1)(2 log Π_jW_j^{2t} + 3) = O(L⁴)`. The cube absorption `c·X³ ≤ n/32 + K₀` (`cube_absorb`) turns
`2^{O(L³)}` into the capacity's `2^{⌊n/16⌋ + d_C L²}` under a floor fixed before `F`.

* `cube_le_two_pow_half`, **`cube_absorb`**, `frame_len`, `cH`, `cHt`, `c0S`, `cS`;
* `cells_le`, `twoT_le`, **`htW_le`**, `popsW_le`, `wtW_le`, **`hbS_le`**.

Paper quantities of the main types: the Hb printer's size at a HASH call against `2^{O(k + L³)}`. -/

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

/-- The HASH rows' monomial-count exponent constant. -/
noncomputable def cH (l : Literals) : ℕ := 31 * (192 * cE l + 385)
/-- The HASH tape's word exponent constant. -/
noncomputable def cHt (l : Literals) : ℕ := cN l + cH l + 192 * cE l + 385 + 39
/-- The sum of the pieces' constants. -/
noncomputable def c0S (l : Literals) : ℕ :=
  cV l + cHt l + (24 * CallIndex.algX l + 127) + cJ l + 2 * cPW l + 29 + cN l
/-- **The Hb size's constant** `c_S`. -/
noncomputable def cS (l : Literals) : ℕ := c0S l + 4

section Gate
variable (l : Literals) (F : GateFree l)

theorem cells_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    2 ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t + 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) * ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J + 1) * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops.length * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 ≤
      2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
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
  have hlt : 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t + 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) + 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    rw [ht']
    have h1 : 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul (by omega) hl0
    have e : 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) = 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
    omega
  have hE1 : 2 ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t + 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) ≤ 2 ^ (2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) + 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) :=
    Nat.pow_le_pow_right (by norm_num) hlt
  have key := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hE1 hJ1) hP) hnE') (le_of_eq hN)
  refine key.trans ?_
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
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

theorem twoT_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    2 ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t + 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) ≤ 2 ^ (cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) ∧ 2 ^ ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 + 1) ≤ 2 ^ (cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
  have ht := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hl0 := ell0_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have ht' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
  have hXX : ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have hlt : 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t + 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) + 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    rw [ht']
    have h1 : 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul (by omega) hl0
    have e : 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) = 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
    omega
  have i3 : 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) ≤ 2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have : cT l * ((Nat.clog 2 (n + 2)) + 1) ≤ cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXX
    have e : 2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = 2 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by ring
    omega
  have e : cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (24 * (CallIndex.algX l) + 66) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) +
      2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by unfold cV; ring
  have hL0 : cL0 l * ((Nat.clog 2 (n + 2)) + 1) + 1 ≤ cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (24 * (CallIndex.algX l) + 66) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have h1 : cL0 l * ((Nat.clog 2 (n + 2)) + 1) ≤ cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXX
    have h2 : 30 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ (24 * (CallIndex.algX l) + 66) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_right _ (by omega)
    have e2 : cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 29 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by unfold cL0; ring
    omega
  refine ⟨Nat.pow_le_pow_right (by norm_num) (by rw [e]; omega), Nat.pow_le_pow_right (by norm_num) ?_⟩
  rw [e]; omega

/-- **The HASH tape's word** `≤ 2^{2k + c_{Ht} X³}`. -/
theorem htW_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : (PrimT.HbM.htWord (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs).length ≤ 2 ^ (2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cHt l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
  have hkh := kh_two l F kclk coef A a ha hs
  have hnE := nE_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have he := E_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hsx := sumX_le l F kclk coef A a ha ha' Cs carriers translation hcall
  have hGl := G_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL1 : 1 ≤ (Nat.clog 2 (n + 2)) := one_le_L n
  have hG : 2 * (carriers.map List.length).sum ≤ (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length := by rw [pool_length]; omega
  have hmem := hashFs_mem ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) (PrimAsm.WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (PrimAsm.WriterIface.auxEnum (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length n hG
  obtain ⟨D1, hD1d⟩ : ∃ D1, D1 = 384 * (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 1 := ⟨_, rfl⟩
  obtain ⟨A1, hA1d⟩ : ∃ A1, A1 = 4 * (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) ^ 2 * (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length := ⟨_, rfl⟩
  obtain ⟨K1, hK1d⟩ : ∃ K1, K1 = (4 * (2 * (carriers.map List.length).sum) + 1) ^ D1 := ⟨_, rfl⟩
  rw [← hD1d, ← hA1d] at hmem
  have hPW : ∀ p ∈ (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs, (ListMachine.Rec.polyWord p).length ≤ K1 * (2 * D1 * (A1 + 1) + 2) + 1 := fun p hp =>
    PrimAsm.BShape.polyWord_le p D1 A1 K1 (le_trans (hmem p hp).2 (le_of_eq hK1d.symm)) (hmem p hp).1
  have hht := htWord_le (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs _ hPW
  have hFl : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs.length = (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) ^ 2 * (PrimAsm.WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := by
    show ((PrimAsm.Batch.hashBatch ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) (PrimAsm.WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (PrimAsm.WriterIface.auxEnum (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length n).map PrimT.C4H.rowPoly).length = _
    simp [PrimAsm.Batch.hashBatch]
  rw [hFl] at hht
  -- the numbers
  have hN : (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) ^ 2 = 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) := by rw [← pow_mul, ← hkh, Nat.mul_comm]
  have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
  have hXX : ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have hXXX : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_right _ (by omega)
  have hD1 : D1 ≤ (192 * cE l + 385) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have hw : (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen = 2 * ((Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) / 4) + 1 := rfl
    rw [hD1d, hw]
    have h1 : 192 * (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 192 * (cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := Nat.mul_le_mul_left _ he
    have hXX1 : 1 ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul hX1 hX1
    have e : (192 * cE l + 385) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = 192 * (cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) + 385 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
    omega
  have h8 : 4 * (2 * (carriers.map List.length).sum) + 1 ≤ 2 ^ (5 + 26 * (Nat.clog 2 (n + 2))) := by
    rw [pow_add]; have : 1 ≤ (2 : ℕ) ^ (26 * (Nat.clog 2 (n + 2))) := Nat.one_le_two_pow; omega
  have hK1 : K1 ≤ 2 ^ (cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
    rw [hK1d]
    refine (pow_mono_mul D1 h8).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    calc D1 * (5 + 26 * (Nat.clog 2 (n + 2))) ≤ (192 * cE l + 385) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) * (31 * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul hD1 (by omega)
      _ = cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by unfold cH; ring
  have hA1 : A1 + 1 ≤ 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2))) := by
    rw [hA1d, hN]
    have : (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 2 ^ (3 + 26 * (Nat.clog 2 (n + 2))) := hGl
    have e : (2 : ℕ) ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2))) = 8 * (2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * 2 ^ (3 + 26 * (Nat.clog 2 (n + 2)))) := by
      rw [show (((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2)) = (((gate0 l F).budget kclk coef A a ha).kOf n) + (3 + 26 * (Nat.clog 2 (n + 2))) + 3 by ring, pow_add, pow_add]; ring
    rw [e]
    have h1 : 4 * 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 4 * (2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * 2 ^ (3 + 26 * (Nat.clog 2 (n + 2)))) := by
      have := Nat.mul_le_mul_left (2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n)) this
      calc 4 * 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length = 4 * (2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ this
    have h2 : 1 ≤ 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * 2 ^ (3 + 26 * (Nat.clog 2 (n + 2))) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hDA : 2 * D1 * (A1 + 1) + 2 ≤ 2 ^ (D1 + (((gate0 l F).budget kclk coef A a ha).kOf n) + 8 + 26 * (Nat.clog 2 (n + 2))) := by
    have hd : D1 ≤ 2 ^ D1 := Nat.lt_two_pow_self.le
    have e : (2 : ℕ) ^ (D1 + (((gate0 l F).budget kclk coef A a ha).kOf n) + 8 + 26 * (Nat.clog 2 (n + 2))) = 4 * (2 ^ D1 * 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2)))) := by
      rw [show D1 + (((gate0 l F).budget kclk coef A a ha).kOf n) + 8 + 26 * (Nat.clog 2 (n + 2)) = D1 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2))) + 2 by ring, pow_add, pow_add]; ring
    rw [e]
    have h1 : D1 * (A1 + 1) ≤ 2 ^ D1 * 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul hd hA1
    have h2 : 1 ≤ 2 ^ D1 * 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2))) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have e2 : 2 * D1 * (A1 + 1) = 2 * (D1 * (A1 + 1)) := by ring
    omega
  obtain ⟨EW, hEW⟩ : ∃ EW, EW = cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (D1 + (((gate0 l F).budget kclk coef A a ha).kOf n) + 8 + 26 * (Nat.clog 2 (n + 2))) := ⟨_, rfl⟩
  have hPW2 : K1 * (2 * D1 * (A1 + 1) + 2) + 1 + 12 ≤ 2 ^ (EW + 4) := by
    have h1 : K1 * (2 * D1 * (A1 + 1) + 2) ≤ 2 ^ EW := by
      rw [hEW, pow_add]; exact Nat.mul_le_mul hK1 hDA
    have h2 : 1 ≤ (2 : ℕ) ^ EW := Nat.one_le_two_pow
    rw [pow_add]; omega
  have hF2 : (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) ^ 2 * (PrimAsm.WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
    rw [hN, pow_add]; exact Nat.mul_le_mul_left _ hnE
  have hfin : (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) ^ 2 * (PrimAsm.WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (K1 * (2 * D1 * (A1 + 1) + 2) + 1 + 12) + 1 ≤
      2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (EW + 4) + 1) := by
    have h1 := Nat.mul_le_mul hF2 hPW2
    have h2 : 1 ≤ (2 : ℕ) ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) * 2 ^ (EW + 4) := Nat.mul_le_mul Nat.one_le_two_pow Nat.one_le_two_pow
    have e : (2 : ℕ) ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (EW + 4) + 1) = 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) * 2 ^ (EW + 4) * 2 := by
      rw [← pow_add, ← pow_succ]
    rw [e]; omega
  refine hht.trans (hfin.trans (Nat.pow_le_pow_right (by norm_num) ?_))
  rw [hEW]
  have i1 : cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXXX
  have i2 : D1 ≤ (192 * cE l + 385) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := hD1.trans (Nat.mul_le_mul_left _ hXXX)
  have i3 : 26 * (Nat.clog 2 (n + 2)) + 13 ≤ 39 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have : ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := hXX.trans hXXX
    omega
  have e : cHt l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (192 * cE l + 385) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 39 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    unfold cHt; ring
  rw [e]; omega

theorem popsW_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (PrimT.HbM.popsWord (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops).length ≤ 2 ^ ((24 * (CallIndex.algX l) + 127) * ((Nat.clog 2 (n + 2)) + 1)) := by
  have hA := A_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hM := M_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hGl := G_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hmem : ∀ pop ∈ (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops, pop.2.length ≤ (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ∧ ∀ gi ∈ pop.2, gi < (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length :=
    fun pop hp => mem_hashPops (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers pop hp
  have h := popsWord_le (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length hmem
  have hP : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops.length ≤ 2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) := by
    show (PrimT.C4H.hashPopsOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).length ≤ _
    rw [hashPops_length]; exact hA
  have hG1 : (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length + 1 ≤ 2 ^ (4 + 26 * (Nat.clog 2 (n + 2))) := by
    rw [pow_add]; have : 1 ≤ (2 : ℕ) ^ (26 * (Nat.clog 2 (n + 2))) := Nat.one_le_two_pow
    rw [pow_add] at hGl; omega
  have hMG : 3 + (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) * ((PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length + 1) ≤ 2 ^ (28 * ((Nat.clog 2 (n + 2)) + 1) + (4 + 26 * (Nat.clog 2 (n + 2))) + 2) := by
    have h1 : (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) * ((PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length + 1) ≤ 2 ^ (28 * ((Nat.clog 2 (n + 2)) + 1)) * 2 ^ (4 + 26 * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul hM hG1
    have h2 : 1 ≤ (2 : ℕ) ^ (28 * ((Nat.clog 2 (n + 2)) + 1)) * 2 ^ (4 + 26 * (Nat.clog 2 (n + 2))) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [pow_add, pow_add]; omega
  have h3 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops.length * (3 + (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) * ((PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length + 1)) + 1 ≤
      2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2 + (28 * ((Nat.clog 2 (n + 2)) + 1) + (4 + 26 * (Nat.clog 2 (n + 2))) + 2) + 1) := by
    have h1 := Nat.mul_le_mul hP hMG
    have h2 : 1 ≤ (2 : ℕ) ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) * 2 ^ (28 * ((Nat.clog 2 (n + 2)) + 1) + (4 + 26 * (Nat.clog 2 (n + 2))) + 2) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [pow_succ, pow_add]; omega
  refine h.trans (h3.trans (Nat.pow_le_pow_right (by norm_num) ?_))
  have e : (24 * (CallIndex.algX l) + 127) * ((Nat.clog 2 (n + 2)) + 1) = (24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + (24 * (CallIndex.algX l) + 64) + 63 * (Nat.clog 2 (n + 2)) + 63 := by ring
  rw [e]; omega

theorem wtW_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (PrimT.HbM.wtWord (PrimT.HbM.wsOf (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP)).length ≤ 2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1) + (2 * cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 3)) := by
  have hJ := J_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hW := prodW_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hJ' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J = (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have hbits : ∀ w ∈ PrimT.HbM.wsOf (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP, w.length ≤ cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 1 := by
    intro w hw
    unfold PrimT.HbM.wsOf at hw
    obtain ⟨lam, hlam, rfl⟩ := List.mem_map.mp hw
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    have h1 : (if lam < (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J then SeedFix.clearW (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP lam else SeedFix.prodW (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP) ≤
        SeedFix.prodW (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP := by
      split_ifs with h
      · exact SeedFix.clearW_le (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP lam h
      · exact le_rfl
    calc _ ≤ SeedFix.prodW (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP := h1
      _ ≤ 2 ^ (cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := hW
      _ < 2 ^ (cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  unfold PrimT.HbM.wtWord
  rw [List.length_flatMap]
  have hsum := PrimAsm.BShape.sum_map_le_card (PrimT.HbM.wsOf (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP) (fun w => (RepairOrdinary.frame w).length)
    (2 * (cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 1) + 1) (fun w hw => by
      show (RepairOrdinary.frame w).length ≤ _
      rw [frame_len]; have := hbits w hw; omega)
  have hlen : (PrimT.HbM.wsOf (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP).length = (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 := by
    unfold PrimT.HbM.wsOf; rw [List.length_map, List.length_range, hJ']
  rw [hlen] at hsum
  have hJ1 : (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 ≤ 2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1)) := (Nat.add_le_add_right hJ 1).trans Nat.lt_two_pow_self
  have hb : 2 * (cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 1) + 1 ≤ 2 ^ (2 * cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 3) := by
    have h1 : 2 * cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 3 < 2 ^ (2 * cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 3) := Nat.lt_two_pow_self
    have e : 2 * (cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 1) + 1 = 2 * cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 3 := by ring
    omega
  refine hsum.trans ?_
  rw [pow_add]
  exact Nat.mul_le_mul hJ1 hb

/-- **The Hb size at a THR call** `hbS ≤ 2^{2k + c_S X³}`. -/
theorem hbS_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 2 ^ (2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cS l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
  have p1 := cells_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have p2 := twoT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have p4 := htW_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have p5 := popsW_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have p6 := wtW_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have p7 := G_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hnE := nE_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hN : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 = 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) := by
    show (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) ^ 2 = _
    rw [← pow_mul, ← hkh, Nat.mul_comm]
  have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
  have hXX : ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have hXXX : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨E0, hE0⟩ : ∃ E0, E0 = 2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + c0S l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := ⟨_, rfl⟩
  have hc0 : cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cHt l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (24 * (CallIndex.algX l) + 127) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 2 * cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) +
      29 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = c0S l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by unfold c0S; ring
  have q : ∀ e, e ≤ E0 → 2 ^ e ≤ 2 ^ E0 := fun e h => Nat.pow_le_pow_right (by norm_num) h
  have i1 : cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXXX
  have i2 : (24 * (CallIndex.algX l) + 127) * ((Nat.clog 2 (n + 2)) + 1) ≤ (24 * (CallIndex.algX l) + 127) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ (hXX.trans hXXX)
  have i3 : cJ l * ((Nat.clog 2 (n + 2)) + 1) ≤ cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ (hXX.trans hXXX)
  have i4 : cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXXX
  have i5 : 3 + 26 * (Nat.clog 2 (n + 2)) ≤ 29 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by have : ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := hXX.trans hXXX; omega
  have i6 : 2 * cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 3 ≤ 2 * cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 29 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have : 1 ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := hX1.trans (hXX.trans hXXX); omega
  have b1 := p1.trans (q _ (by omega))
  have b2 := p2.1.trans (q _ (by omega))
  have b3 := p2.2.trans (q _ (by omega))
  have b4 := p4.trans (q _ (by omega))
  have b5 := p5.trans (q _ (by omega))
  have b6 := p6.trans (q _ (by omega))
  have b7 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G ≤ 2 ^ E0 := p7.trans (q _ (by omega))
  have b8 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 ≤ 2 ^ E0 := by rw [hN]; exact q _ (by omega)
  have b9 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE ≤ 2 ^ E0 := hnE.trans (q _ (by omega))
  have e16 : 16 * 2 ^ E0 ≤ 2 ^ (2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cS l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
    have h1 : 2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cS l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = E0 + 4 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by rw [hE0]; unfold cS; ring
    have h2 : E0 + 4 ≤ E0 + 4 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
      have : 1 ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := hX1.trans (hXX.trans hXXX)
      omega
    calc 16 * 2 ^ E0 = 2 ^ (E0 + 4) := by rw [pow_add]; ring
      _ ≤ 2 ^ (E0 + 4 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := Nat.pow_le_pow_right (by norm_num) h2
      _ = _ := by rw [h1]
  unfold PrimT.C4H.hbS
  omega

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr

end
