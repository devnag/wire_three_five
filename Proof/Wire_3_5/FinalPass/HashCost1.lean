import Lean
import Proof.Wire_3_5.FinalPass.HashS
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashPre1
import Proof.Wire_3_5.FinalPass.HashSz1
import Proof.Wire_3_5.FinalPass.HashSz2
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.HashCost1Base


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH child's cost, part 1: the printed objective's word at a THR call

The HASH child's steps (`C4H.hCoreCost`, P3:2253-2290, 3011-3016) read the printed objective's word
`exprWord (hV D p')`. Every printed term has coefficient `|c| ≤ Π_jW_j^{2t}·2^{2tℓ₀}` (the coefficient word is
`2·size|c| + 3` bits), `1 + 2t` factors, each an aux FILTER row (`≤ (8Σ|X_j|+1)^{384w+1}` monomials) or a corner form
(`10` monomials), all of degree `≤ 384w + 1` over atoms below `4N²G`; so the word has at most `2^{2k + c_W X³}` bits.

* `zPoly_length`, `hashFactor_len`, `coefWord_len`, `termWord_le'`, `cW2`;
* `walkD_le`, `atomA_le`, `fsLen_le`, **`ew_le`**.

Paper quantity of the main type: the printed HASH objective's word length. -/

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

/-- The printed word's exponent constant. -/
noncomputable def cW2 (l : Literals) : ℕ :=
  cV l + cH l + (192 * cE l + 385) + cPW l + 2 * cT l * cL0 l + 4 * cT l + 60

section Gate
variable (l : Literals) (F : GateFree l)

theorem walkD_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : 384 * (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 1 ≤ (192 * cE l + 385) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
  have he := E_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hw : (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen = 2 * ((Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) / 4) + 1 := rfl
  rw [hw]
  have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
  have h1 : 192 * (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 192 * (cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := Nat.mul_le_mul_left _ he
  have hXX1 : 1 ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul hX1 hX1
  have e : (192 * cE l + 385) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = 192 * (cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) + 385 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
  omega

theorem atomA_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : 4 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G + 1 ≤ 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2))) := by
  have hkh := kh_two l F kclk coef A a ha hs
  have hGl := G_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hN : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 = 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) := by
    show (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) ^ 2 = _
    rw [← pow_mul, ← hkh, Nat.mul_comm]
  have hG' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G ≤ 2 ^ (3 + 26 * (Nat.clog 2 (n + 2))) := hGl
  rw [hN]
  have e : (2 : ℕ) ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2))) = 8 * (2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * 2 ^ (3 + 26 * (Nat.clog 2 (n + 2)))) := by
    rw [show (((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2)) = (((gate0 l F).budget kclk coef A a ha).kOf n) + (3 + 26 * (Nat.clog 2 (n + 2))) + 3 by ring, pow_add, pow_add]; ring
  rw [e]
  have h1 : 4 * 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G ≤ 4 * (2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * 2 ^ (3 + 26 * (Nat.clog 2 (n + 2)))) := by
    calc 4 * 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G = 4 * (2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hG')
  have h2 : 1 ≤ 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n) * 2 ^ (3 + 26 * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul Nat.one_le_two_pow Nat.one_le_two_pow
  omega

/-- **The HASH rows' monomial counts** `≤ 2^{c_H X³}`. -/
theorem fsLen_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : ∀ i, ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs.getD i []).length ≤ 2 ^ (cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
  have hsx := sumX_le l F kclk coef A a ha ha' Cs carriers translation hcall
  have hL1 : 1 ≤ (Nat.clog 2 (n + 2)) := one_le_L n
  have hG : 2 * (carriers.map List.length).sum ≤ (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length := by rw [pool_length]; omega
  have hmem := hashFs_mem ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) (PrimAsm.WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (PrimAsm.WriterIface.auxEnum (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length n hG
  have hD1 := walkD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have h8 : 4 * (2 * (carriers.map List.length).sum) + 1 ≤ 2 ^ (5 + 26 * (Nat.clog 2 (n + 2))) := by
    rw [pow_add]; have : 1 ≤ (2 : ℕ) ^ (26 * (Nat.clog 2 (n + 2))) := Nat.one_le_two_pow; omega
  have hK : (4 * (2 * (carriers.map List.length).sum) + 1) ^ (384 * (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 1) ≤ 2 ^ (cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
    refine (pow_mono_mul (384 * (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 1) h8).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
    calc (384 * (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 1) * (5 + 26 * (Nat.clog 2 (n + 2))) ≤ (192 * cE l + 385) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) * (31 * ((Nat.clog 2 (n + 2)) + 1)) :=
          Nat.mul_le_mul hD1 (by omega)
      _ = cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by unfold cH; ring
  intro i
  by_cases hi : i < (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact le_trans (hmem _ (List.getElem_mem hi)).2 hK
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

/-- **The printed HASH objective's word** `≤ 2^{2k + c_{W2} X³}` at every prefix of at most `2tℓ₀` bits. -/
theorem ew_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (p' : List Bool) (hp : p'.length ≤ 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) :
    (ListMachine.Rec.exprWord (PrimT.C4H.hV (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p')).length ≤ 2 ^ (2 * (((gate0 l F).budget kclk coef A a ha).kOf n) + cW2 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
  have hV := lenV_le l F kclk coef A a ha ha' Cs carriers translation hcall hs p'.length (SeedFix.listNum p')
  have hW := prodW_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have htl := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hl0 := ell0_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hD1 := walkD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hA1 := atomA_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hFl := fsLen_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hsx := sumX_le l F kclk coef A a ha ha' Cs carriers translation hcall
  have hL1 : 1 ≤ (Nat.clog 2 (n + 2)) := one_le_L n
  have ht' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have hG : 2 * (carriers.map List.length).sum ≤ (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length := by rw [pool_length]; omega
  have hFs : ∀ i, PrimAsm.BShape.PolyOk (384 * (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 1) (4 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G) ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs.getD i []) :=
    hashFs_getD ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))) (PrimAsm.WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (PrimAsm.WriterIface.auxEnum (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length n hG
  have hpop : ∀ pop ∈ (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops, ∀ gi ∈ pop.2, gi < (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G := fun pop hpop =>
    (mem_hashPops (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers pop hpop).2
  have hw1 : 1 ≤ (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen := by
    show 1 ≤ 2 * ((Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) / 4) + 1
    omega
  -- the numbers
  have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
  have hXX : ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have hXXX : (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨D1, hD1d⟩ : ∃ D1, D1 = 384 * (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 1 := ⟨_, rfl⟩
  obtain ⟨A1, hA1d⟩ : ∃ A1, A1 = 4 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G := ⟨_, rfl⟩
  rw [← hD1d] at hD1 hFs
  rw [← hA1d] at hA1 hFs
  -- every factor's word
  obtain ⟨PWe, hPWe⟩ : ∃ PWe, PWe = cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 4 + (D1 + (((gate0 l F).budget kclk coef A a ha).kOf n) + 8 + 26 * (Nat.clog 2 (n + 2))) := ⟨_, rfl⟩
  have hPW : ∀ t ∈ PrimT.C4H.hV (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p', ∀ f ∈ t.2, (ListMachine.Rec.polyWord f).length + 1 ≤ 2 ^ (PWe + 1) := by
    intro t ht f hf
    have hok := hashFactor_ok (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops p'.length (SeedFix.listNum p') D1 A1
      (by omega) (by rw [hA1d]) hFs hpop t ht f hf
    have hlen := hashFactor_len (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops p'.length (SeedFix.listNum p')
      (2 ^ (cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)))) hFl t ht f hf
    have hpw := PrimAsm.BShape.polyWord_le f D1 A1 _ hlen hok
    have hd : D1 ≤ 2 ^ D1 := Nat.lt_two_pow_self.le
    have hDA : 2 * D1 * (A1 + 1) + 2 ≤ 2 ^ (D1 + (((gate0 l F).budget kclk coef A a ha).kOf n) + 8 + 26 * (Nat.clog 2 (n + 2))) := by
      have e : (2 : ℕ) ^ (D1 + (((gate0 l F).budget kclk coef A a ha).kOf n) + 8 + 26 * (Nat.clog 2 (n + 2))) = 4 * (2 ^ D1 * 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2)))) := by
        rw [show D1 + (((gate0 l F).budget kclk coef A a ha).kOf n) + 8 + 26 * (Nat.clog 2 (n + 2)) = D1 + ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2))) + 2 by ring, pow_add, pow_add]; ring
      rw [e]
      have h1 : D1 * (A1 + 1) ≤ 2 ^ D1 * 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul hd hA1
      have h2 : 1 ≤ 2 ^ D1 * 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + 6 + 26 * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul Nat.one_le_two_pow Nat.one_le_two_pow
      have e2 : 2 * D1 * (A1 + 1) = 2 * (D1 * (A1 + 1)) := by ring
      omega
    have hK10 : 2 ^ (cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) + 10 ≤ 2 ^ (cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 4) := by
      rw [pow_add]; have : 1 ≤ (2 : ℕ) ^ (cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := Nat.one_le_two_pow; omega
    have hm : (2 ^ (cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) + 10) * (2 * D1 * (A1 + 1) + 2) ≤ 2 ^ PWe := by
      rw [hPWe, pow_add]; exact Nat.mul_le_mul hK10 hDA
    have h1 : 2 ≤ (2 : ℕ) ^ PWe :=
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ PWe := Nat.pow_le_pow_right (by norm_num) (by rw [hPWe]; omega)
    rw [pow_succ]; omega
  -- every term's word
  obtain ⟨ce, hce⟩ : ∃ ce, ce = cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 1 := ⟨_, rfl⟩
  have hTW : ∀ t ∈ PrimT.C4H.hV (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p', (ListMachine.Rec.termWord t).length ≤
      2 * ce + 3 + (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) * (2 ^ (PWe + 1)) + 1 := by
    intro t ht
    have hc := hashTerm_coef (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).G (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).N (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).nE (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).Fs (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).pops p'.length (SeedFix.listNum p') hp t ht
    have hlt : 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
      rw [ht']
      calc 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) * (cL0 l * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ htl) hl0
        _ = 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by ring
    have hc2 : t.1.natAbs < 2 ^ ce := by
      have h1 : t.1.natAbs ≤ 2 ^ (cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) * 2 ^ (2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) :=
        hc.trans (Nat.mul_le_mul hW (Nat.pow_le_pow_right (by norm_num) hlt))
      rw [← pow_add] at h1
      rw [hce]
      exact lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hWl : t.2.length ≤ 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 := by
      rw [PrimT.HashB.hashTermsM_uniform _ _ _ _ _ _ _ _ t ht, ht']; omega
    have h := termWord_le' t ce (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) (2 ^ (PWe + 1) - 1) hc2 hWl (fun f hf => by
      have := hPW t ht f hf; omega)
    have e : 2 ^ (PWe + 1) - 1 + 1 = 2 ^ (PWe + 1) := by
      have : 1 ≤ (2 : ℕ) ^ (PWe + 1) := Nat.one_le_two_pow
      omega
    rw [e] at h
    exact h
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = (2 : ℕ) ^ (PWe + 1) := ⟨_, rfl⟩
  rw [← hP1] at hTW
  have hew := PrimAsm.BShape.exprWord_le (PrimT.C4H.hV (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) p') _ _ hV hTW
  refine hew.trans ?_
  -- the arithmetic
  have hT2 : 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 ≤ 2 ^ (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) := by
    have h1 : 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 ≤ 2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1 := by
      have e : 2 * cT l * ((Nat.clog 2 (n + 2)) + 1) = 2 * (cT l * ((Nat.clog 2 (n + 2)) + 1)) := by ring
      omega
    exact h1.trans (Nat.lt_two_pow_self).le
  have hA2 : 2 ≤ 2 ^ (ce + 3) :=
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (ce + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hP1' : 1 ≤ P1 := by rw [hP1]; exact Nat.one_le_two_pow
  have hB2 : 2 ≤ 2 ^ (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) * P1 := by
    have h1 : 2 ≤ 2 ^ (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) :=
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact h1.trans (Nat.le_mul_of_pos_right _ hP1')
  have hce2 : 2 * ce + 3 + 1 + 1 ≤ 2 ^ (ce + 3) := by
    have := Nat.lt_two_pow_self (n := ce)
    rw [pow_add]; omega
  have hb : (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) * P1 ≤ 2 ^ (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) * P1 := Nat.mul_le_mul_right _ hT2
  have hAB := Nat.add_le_mul hA2 hB2
  have hTWb : 2 * ce + 3 + (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) * P1 + 1 + 1 ≤ 2 ^ (ce + 3) * (2 ^ (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) * P1) := by
    omega
  have hfin : 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) * (2 * ce + 3 + (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) * P1 + 1 + 1) + 1 ≤
      2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) * (2 ^ (ce + 3) * (2 ^ (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) * P1)) * 2 := by
    have h1 := Nat.mul_le_mul_left (2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)))) hTWb
    have h2 : 1 ≤ 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) * (2 ^ (ce + 3) * (2 ^ (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) * P1)) :=
      Nat.mul_le_mul Nat.one_le_two_pow (Nat.mul_le_mul Nat.one_le_two_pow (Nat.mul_le_mul Nat.one_le_two_pow hP1'))
    omega
  have hfe : 2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) * (2 ^ (ce + 3) * (2 ^ (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) * P1)) * 2 =
      2 ^ ((((gate0 l F).budget kclk coef A a ha).kOf n) + cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (ce + 3) + (2 * cT l * ((Nat.clog 2 (n + 2)) + 1) + 1) + (PWe + 1) + 1) := by
    rw [hP1]; ring
  refine (hfin.trans (le_of_eq hfe)).trans (Nat.pow_le_pow_right (by norm_num) ?_)
  rw [hce, hPWe]
  have i1 : D1 ≤ (192 * cE l + 385) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := hD1.trans (Nat.mul_le_mul_left _ hXXX)
  have i2 : cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXXX
  have i3 : 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) ≤ 2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXXX
  have i4 : 2 * cT l * ((Nat.clog 2 (n + 2)) + 1) ≤ 2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ (hXX.trans hXXX)
  have i5 : 26 * (Nat.clog 2 (n + 2)) + 30 ≤ 56 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have : ((Nat.clog 2 (n + 2)) + 1) ≤ (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := hXX.trans hXXX
    omega
  have e : cW2 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = cV l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cH l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + (192 * cE l + 385) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) +
      2 * cT l * cL0 l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 2 * (2 * cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) + 60 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by unfold cW2; ring
  rw [e]
  omega

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr

end
